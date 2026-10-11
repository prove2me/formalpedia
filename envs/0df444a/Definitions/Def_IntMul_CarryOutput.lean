-- Prove2me | Definitions.Def_IntMul_CarryOutput
-- name    : IntMul_CarryOutput
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T13:00:36.813861+00:00
-- url     : https://prove2.me/theorems/3c346fb4-3212-4cb0-b3f8-49659d9b305d
-- title:
--   Complete physical carry traversal and big-endian output return on the same fifteen tapes
-- statement:
--   A fixed fifteen-tape machine executes the complete finite coefficient-list carry traversal and then physically returns the emitted low digits in big-endian order. Both native machines use the same real tapes and alphabet; the combined finite transition table copies their actions verbatim. Two charged finite-caller returns join them and reach global halt. The incoming coefficient/carry/descriptor frame and the entire terminal caller frame are explicit. Coefficient generation and global initialization are separate obligations. Correctness, mathematical carry-scan agreement and the complete linear clock are proved separately.
-- source:
--   Original complete same-tape physical carry normalization and output order return. Uses literal native transition tables with finite tags and paid caller returns. Written by Codex.

import Definitions.Def_IntMul_CarryBatch
import Definitions.Def_IntMul_CanonicalOutput

set_option maxHeartbeats 1000000
set_option Elab.async false

namespace IntMul.CarryOutput
open TapeCopy (Sym)

abbrev State := Option (CarryBatch.machine.K ⊕ CanonicalOutput.machine.K)

noncomputable def batchState (q : CarryBatch.machine.K) : State :=
  if q=none then none else some (.inl q)

noncomputable def outputState (q : CanonicalOutput.machine.K) : State :=
  if q=none then none else some (.inr q)

/-- Both actual transition tables operate on the same fifteen physical tapes.
Only the finite state tag changes; every physical action is copied verbatim. -/
noncomputable def transition (q : State) (a : Fin 15 → Sym) :
    State × (Fin 15 → Sym × Move) :=
  match q with
  | none => (none,fun i => (a i,.stay))
  | some (.inl q) =>
      let r := CarryBatch.machine.δ q a
      (batchState r.1,r.2)
  | some (.inr q) =>
      let r := CanonicalOutput.machine.δ q a
      (outputState r.1,r.2)

noncomputable abbrev subroutine : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := batchState CarryBatch.machine.qStart
  qHalt := none
  start_ne_halt := by simp only [batchState,CarryBatch.machine,FiniteCaller.machine,reduceCtorEq,if_false];exact Option.some_ne_none _
  k := 15
  two_le_k := by decide
  δ := transition
  start_preserved := by
    intro q a i hi
    cases q with
    | none =>
        change a i=Sym.start ∧ Move.stay≠Move.left
        exact ⟨hi,by decide⟩
    | some s =>
        cases s with
        | inl q => exact CarryBatch.machine.start_preserved q a i hi
        | inr q => exact CanonicalOutput.machine.start_preserved q a i hi
  start_only_at_start := by
    intro q a i hi
    cases q with
    | none => exact hi
    | some s =>
        cases s with
        | inl q => exact CarryBatch.machine.start_only_at_start q a i hi
        | inr q => exact CanonicalOutput.machine.start_only_at_start q a i hi
  halt_fixed := by intro a;rfl
  input_readonly := by
    intro q a
    cases q with
    | none => rfl
    | some s =>
        cases s with
        | inl q => exact CarryBatch.machine.input_readonly q a
        | inr q => exact CanonicalOutput.machine.input_readonly q a

inductive Phase | carry | order deriving DecidableEq

instance : Fintype Phase where
  elems := {.carry,.order}
  complete := by intro q;cases q <;> simp

noncomputable def dispatch (q : Phase) (_a : Fin 15 → Sym) : Option (Phase × State) :=
  match q with
  | .carry => some (.order,outputState CanonicalOutput.machine.qStart)
  | .order => none

noncomputable abbrev machine : MultitapeTM := FiniteCaller.machine subroutine Phase .carry dispatch

noncomputable def batchView (c : CarryBatch.machine.Cfg) : subroutine.Cfg where
  state := batchState c.state
  cells := c.cells
  head := c.head

noncomputable def outputView (c : CanonicalOutput.machine.Cfg) : subroutine.Cfg where
  state := outputState c.state
  cells := c.cells
  head := c.head

/-- Complete prepared carry input, with every incoming descriptor and cursor
explicit. No initialization or free tape loading is asserted by this frame. -/
noncomputable def initialFrame (pre : List Bool) (xs : List (List Bool))
    (a y z l : List Bool) : machine.Cfg :=
  FiniteCaller.embed subroutine Phase .carry .carry dispatch
    (batchView (CarryBatch.initialFrame pre xs a y z l))

noncomputable def outputBase (pre : List Bool) (xs : List (List Bool))
    (a y z l : List Bool) : CanonicalOutput.machine.Cfg where
  state := none
  cells := (CarryBatch.finalFrame pre xs a y z l).cells
  head := (CarryBatch.finalFrame pre xs a y z l).head

/-- Mathematical low digits are returned in big-endian order, carry retained,
all work banks empty, width descriptors retained, and the outer machine halted. -/
noncomputable def finalFrame (pre : List Bool) (xs : List (List Bool))
    (a y z l : List Bool) : machine.Cfg where
  state := none
  cells := (CanonicalOutput.finalFrame (outputBase pre xs a y z l)
    (a++(CarryBatch.scanWords z xs y).1)).cells
  head := (CanonicalOutput.finalFrame (outputBase pre xs a y z l)
    (a++(CarryBatch.scanWords z xs y).1)).head

end IntMul.CarryOutput


