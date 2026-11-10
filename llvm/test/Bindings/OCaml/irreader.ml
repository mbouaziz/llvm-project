(* RUN: rm -rf %t && mkdir -p %t && cp %s %t/irreader.ml
 * RUN: %ocamlc -g -w +A -package llvm.irreader -linkpkg %t/irreader.ml -o %t/executable
 * RUN: %t/executable
 * RUN: %ocamlopt -g -w +A -package llvm.irreader -linkpkg %t/irreader.ml -o %t/executable
 * RUN: %t/executable
 * XFAIL: vg_leak
 *)

(* Note: It takes several seconds for ocamlopt to link an executable with
         libLLVMCore.a, so it's better to write a big test than a bunch of
         little ones. *)

open Llvm
open Llvm_irreader

let context = create_context ()

(* Tiny unit test framework - really just to help find which line is busted *)
let print_checkpoints = false

let suite name f =
  if print_checkpoints then
    prerr_endline (name ^ ":");
  f ()

let _ =
  Printexc.record_backtrace true

let insist cond =
  if not cond then failwith "insist"

(* TODO: Replace with Fun.protect when the minimum OCaml version supports it. *)
let protect ~finally f =
  try
    let r = f () in
    finally ();
    r
  with x ->
    finally ();
    raise x


(*===-- IR Reader ---------------------------------------------------------===*)

let test_irreader () =
  begin
    let buf = MemoryBuffer.of_string "@foo = global i32 42" in
    let m = protect ~finally:(fun () -> MemoryBuffer.dispose buf)
              (fun () -> parse_ir_bitcode_or_assembly context buf) in
    protect ~finally:(fun () -> dispose_module m) (fun () ->
      match lookup_global "foo" m with
      | Some foo ->
          insist (global_initializer foo =
                  Some (const_int (i32_type context) 42))
      | None ->
          failwith "global")
  end;

  begin
    let buf = MemoryBuffer.of_string "@foo = global garble" in
    let parsed = protect ~finally:(fun () -> MemoryBuffer.dispose buf)
                   (fun () ->
                     try
                       let m = parse_ir_bitcode_or_assembly context buf in
                       dispose_module m;
                       true
                     with Llvm_irreader.Error _ ->
                       false)
    in
    if parsed then
      failwith "parsed"
  end


(*===-- Opaque pointers ---------------------------------------------------===*)

(* With opaque pointers, the type of a global's contents, the type a GEP
   indexes, the type an alloca allocates and the callee type of a call are
   properties of the global or instruction, not of a pointer type. Switch case
   values are no longer operands since LLVM 22. *)
let test_opaque_pointer_types () =
  let ir = {|
@g = global [4 x i16] zeroinitializer
declare i32 @printf(ptr, ...)
define void @f(i32 %x) {
entry:
  %a = alloca { i32, double }, i64 3
  %p = getelementptr inbounds [4 x i16], ptr @g, i64 0, i32 %x
  %r = call i32 (ptr, ...) @printf(ptr %p, i32 %x, double 1.0)
  switch i32 %x, label %exit [ i32 7, label %exit
                               i32 9, label %exit ]
exit:
  ret void
}
|} in
  let buf = MemoryBuffer.of_string ir in
  let m = protect ~finally:(fun () -> MemoryBuffer.dispose buf)
            (fun () -> parse_ir_bitcode_or_assembly context buf) in
  protect ~finally:(fun () -> dispose_module m) (fun () ->
    let i16 = i16_type context and i32 = i32_type context in
    let ptr = pointer_type context in
    let g = Option.get (lookup_global "g" m) in
    let printf = Option.get (lookup_function "printf" m) in
    let f = Option.get (lookup_function "f" m) in
    insist (type_of g = ptr);
    insist (global_value_type g = array_type i16 4);
    insist (global_value_type printf = var_arg_function_type i32 [| ptr |]);
    let instrs =
      fold_right_instrs (fun i acc -> i :: acc) (entry_block f) [] in
    match instrs with
    | [ alloca; gep; call; sw ] ->
        insist (get_allocated_type alloca
                = struct_type context [| i32; double_type context |]);
        insist (get_gep_source_element_type gep = array_type i16 4);
        insist (get_called_function_type call
                = var_arg_function_type i32 [| ptr |]);
        insist (num_arg_operands call = 3);
        insist (num_successors sw = 3);
        insist (switch_case_value sw 1 = const_int i32 7);
        insist (switch_case_value sw 2 = const_int i32 9)
    | _ -> failwith "instructions")


(*===-- Driver ------------------------------------------------------------===*)

let _ =
  suite "irreader" test_irreader;
  suite "opaque pointer types" test_opaque_pointer_types;
  dispose_context context
