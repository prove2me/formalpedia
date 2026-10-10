-- Prove2me | Definitions.Def_IntMul_TapeSubtractor
-- name    : IntMul_TapeSubtractor
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T18:43:51.077749+00:00
-- url     : https://prove2.me/theorems/81b7fe46-2e64-4e27-8dae-e0456b9bec4d
-- title:
--   A literal fixed four-tape signed binary subtraction machine
-- statement:
--   Defines one deterministic four-tape machine in the campaign model, with five symbols and eleven states. It copies the first operand onto two work tapes, rewinds the comparison tape, compares the operands from their most significant bits, and computes the absolute difference backwards with a Boolean borrow state. It writes a sign bit followed by the fixed-width magnitude. Its transition function uses only the finite state and scanned symbols; all tape-rule obligations are checked by the constructor. Correctness and the exact transition count are proved separately.
-- source:
--   Explicit implementation of the subtraction half of IntMul.TM.add_sub_linear (https://prove2.me/theorems/02ee99a6-3049-4d13-a20d-ec092f55e29c) for the integer-multiplication κ campaign. It uses the campaign’s IntMul_MultitapeModel, elementary Boolean borrow arithmetic, and finite-state lexicographic comparison. The finite transition table is this formalization’s implementation, not a table asserted by a cited paper.

import Definitions.Def_IntMul_TapeAdder
import Definitions.Def_IntMul_BinarySubtractor

namespace IntMul.TapeSubtractor

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (encode decode safeStep)
open IntMul.BinarySubtractor (Comparison)

inductive State
  | start | copyX | rewind | compare (q : Comparison) | sub (sign borrow : Bool) | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.start, .copyX, .rewind, .compare .lt, .compare .eq, .compare .gt,
    .sub false false, .sub false true, .sub true false, .sub true true, .halt}
  complete := by
    intro q
    cases q with
    | start => simp
    | copyX => simp
    | rewind => simp
    | halt => simp
    | compare q => cases q <;> simp
    | sub s b => cases s <;> cases b <;> simp

/-- Input 0, output 1, low-order arithmetic work tape 2, forward comparison tape 3. -/
def rawTransition (q : State) (a : Fin 4 → Sym) : State × (Fin 4 → Sym × Move) :=
  match q with
  | .halt => (.halt, fun i => (a i, .stay))
  | .start => (.copyX, fun i => (a i, .right))
  | .copyX =>
      if a 0 = .zero ∨ a 0 = .one then
        (.copyX, fun i => (if i = 2 ∨ i = 3 then a 0 else a i, .right))
      else (.rewind, fun i =>
        (a i, if i = 0 then .right else if i = 2 ∨ i = 3 then .left else .stay))
  | .rewind =>
      if a 3 = .start then
        (.compare .eq, fun i => (a i, if i = 3 then .right else .stay))
      else (.rewind, fun i => (a i, if i = 3 then .left else .stay))
  | .compare q =>
      if a 0 = .zero ∨ a 0 = .one then
        (.compare (IntMul.BinarySubtractor.compareStep q (decode (a 3)) (decode (a 0))),
          fun i => (a i, if i = 0 ∨ i = 3 then .right else .stay))
      else (.sub (q == .lt) false, fun i => (a i, if i = 0 then .left else .stay))
  | .sub s b =>
      if a 2 = .start then
        (.halt, fun i => (if i = 1 then encode s else a i, .stay))
      else
        let x := decode (a 2)
        let y := decode (a 0)
        let u := if s then y else x
        let v := if s then x else y
        (.sub s (IntMul.BinarySubtractor.borrowBit u v b), fun i =>
          (if i = 1 then encode (IntMul.BinarySubtractor.diffBit u v b) else a i,
            if i = 3 then .stay else .left))

def transition (q : State) (a : Fin 4 → Sym) : State × (Fin 4 → Sym × Move) :=
  let r := rawTransition q a
  (r.1, fun i => safeStep (a i) (r.2 i).1 (r.2 i).2)

theorem raw_input_readonly (q : State) (a : Fin 4 → Sym) :
    ((rawTransition q a).2 0).1 = a 0 := by
  cases q <;> simp [rawTransition]
  all_goals split <;> simp

abbrev machine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := .start
  qHalt := .halt
  start_ne_halt := by decide
  k := 4
  two_le_k := by decide
  δ := transition
  start_preserved := by
    intro q a i hi
    change (safeStep (a i) _ _).1 = .start ∧ (safeStep (a i) _ _).2 ≠ .left
    rw [hi]
    simp only [safeStep, if_pos rfl]
    by_cases hd : ((rawTransition q a).2 i).2 = Move.left
    · simp [hd]
    · simp [hd]
  start_only_at_start := by
    intro q a i hi
    change (safeStep (a i) _ _).1 ≠ .start
    simp only [safeStep, if_neg hi]
    split <;> assumption
  halt_fixed := by
    intro a
    simp [transition, rawTransition, IntMul.TapeAdder.safe_stay]
  input_readonly := by
    intro q a
    change (safeStep (a 0) ((rawTransition q a).2 0).1 ((rawTransition q a).2 0).2).1 = a 0
    rw [raw_input_readonly]
    exact IntMul.TapeAdder.safe_write_self _ _

end IntMul.TapeSubtractor


