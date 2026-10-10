-- Prove2me | Definitions.Def_IntMul_TapeCopy
-- name    : IntMul_TapeCopy
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T18:01:45.777223+00:00
-- url     : https://prove2.me/theorems/90b8eb1e-ba7f-4c64-832b-51fc4af20cbf
-- title:
--   A literal fixed two-tape operand-copy machine
-- statement:
--   This defines a single deterministic two-tape machine in the integer-multiplication campaign’s multitape model. Its alphabet consists of blank, start marker, the two bits, and the input separator. Its three states are start, copy, and halt. It advances both heads past their start markers, copies input bits onto the output tape while advancing both heads, and halts when it reaches a nonbit. The transition table is explicitly specified, and the constructor checks enforce start-marker preservation, a read-only input tape, and a frozen halt state. Correctness on input x#y and the transition-step bound are proved separately.
-- source:
--   Auxiliary operand-copy primitive for the integer-multiplication κ campaign. The machine model is IntMul_MultitapeModel: https://prove2.me/theorems/47ff1689-4e87-4af2-9406-674787e32429 , following A. Montanaro, Computational Complexity lecture notes (Cambridge, 2012), §3.4. The literal three-state transition table is this formalization’s implementation of the copy primitive, rather than a state table asserted by the paper.

import Definitions.Def_IntMul_MultitapeModel

namespace IntMul.TapeCopy

inductive Sym
  | blank | start | zero | one | sep
  deriving DecidableEq

instance : Fintype Sym where
  elems := {.blank, .start, .zero, .one, .sep}
  complete := by intro x; cases x <;> simp

inductive State
  | start | copy | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.start, .copy, .halt}
  complete := by intro x; cases x <;> simp

/-- This is one fixed two-tape machine, with a five-symbol alphabet. -/
def transition (q : State) (a : Fin 2 → Sym) : State × (Fin 2 → Sym × Move) :=
  match q with
  | .halt => (.halt, fun i => (a i, .stay))
  | .start => (.copy, fun i => (a i, .right))
  | .copy =>
      if a 0 = .zero ∨ a 0 = .one then
        (.copy, fun i =>
          (if i = 0 ∨ a i = .start then a i else a 0, .right))
      else (.halt, fun i => (a i, .stay))

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
  k := 2
  two_le_k := by decide
  δ := transition
  start_preserved := by
    intro q a i hi
    cases q <;> simp [transition, hi]
    split <;> simp [hi]
  start_only_at_start := by
    intro q a i hi
    cases q <;> simp [transition, hi]
    split
    · dsimp only
      split
      · exact hi
      · rename_i hb _
        rcases hb with hz | ho
        · simp [hz]
        · simp [ho]
    · exact hi
  halt_fixed := by intro a; rfl
  input_readonly := by
    intro q a
    cases q <;> simp [transition]
    split <;> simp

end IntMul.TapeCopy


