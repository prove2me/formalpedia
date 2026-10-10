-- Prove2me | Definitions.Def_IntMul_TapeAdder
-- name    : IntMul_TapeAdder
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T18:31:54.247175+00:00
-- url     : https://prove2.me/theorems/07661e9c-97c6-488b-ad10-ecfe3295ddda
-- title:
--   A literal fixed three-tape binary addition machine
-- statement:
--   Defines one deterministic three-tape addition machine in the campaign model, with five symbols and six states. It copies the first operand onto its work tape, scans the second operand, then traverses both operands backwards while carrying one Boolean carry state and writing the sum onto the output tape. Its transition function uses only the finite state and currently scanned symbols. The constructor checks enforce start-marker preservation, read-only input, and a frozen halt state. Correctness and the exact transition count are proved separately.
-- source:
--   Explicit implementation of the addition half of IntMul.TM.add_sub_linear (https://prove2.me/theorems/02ee99a6-3049-4d13-a20d-ec092f55e29c) for the integer-multiplication κ campaign, using IntMul_MultitapeModel and the elementary Boolean full-adder truth table. The finite transition table is this formalization’s implementation, not a table asserted by a cited paper.

import Definitions.Def_IntMul_TapeCopy
import Definitions.Def_IntMul_BinaryAdder

namespace IntMul.TapeAdder

open IntMul.TapeCopy (Sym)

inductive State
  | start | copyX | scanY | add (carry : Bool) | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.start, .copyX, .scanY, .add false, .add true, .halt}
  complete := by
    intro q
    cases q <;> simp


def encode (b : Bool) : Sym := if b then .one else .zero

def decode (s : Sym) : Bool := s == .one

/-- Enforce the campaign's start-marker rules on every configuration. -/
def safeStep (s v : Sym) (d : Move) : Sym × Move :=
  if s = .start then (.start, if d = .left then .stay else d)
  else (if v = .start then s else v, d)

theorem safe_write_self (s : Sym) (d : Move) : (safeStep s s d).1 = s := by
  by_cases hs : s = .start <;> simp [safeStep, hs]

theorem safe_stay (s : Sym) : safeStep s s .stay = (s, .stay) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]

/-- Tape 0 is input, tape 1 output, tape 2 the first-operand work tape. -/
def rawTransition (q : State) (a : Fin 3 → Sym) : State × (Fin 3 → Sym × Move) :=
  match q with
  | .halt => (.halt, fun i => (a i, .stay))
  | .start => (.copyX, fun i => (a i, .right))
  | .copyX =>
      if a 0 = .zero ∨ a 0 = .one then
        (.copyX, fun i => (if i = 2 then a 0 else a i, .right))
      else (.scanY, fun i =>
        (a i, if i = 0 then .right else if i = 2 then .left else .stay))
  | .scanY =>
      if a 0 = .zero ∨ a 0 = .one then
        (.scanY, fun i => (a i, if i = 0 then .right else .stay))
      else (.add false, fun i => (a i, if i = 0 then .left else .stay))
  | .add c =>
      if a 2 = .start then
        (.halt, fun i => (if i = 1 then encode c else a i, .stay))
      else
        (.add (IntMul.BinaryAdder.carryBit (decode (a 2)) (decode (a 0)) c),
          fun i =>
            (if i = 1 then encode (IntMul.BinaryAdder.sumBit (decode (a 2)) (decode (a 0)) c)
             else a i, .left))

def transition (q : State) (a : Fin 3 → Sym) : State × (Fin 3 → Sym × Move) :=
  let r := rawTransition q a
  (r.1, fun i => safeStep (a i) (r.2 i).1 (r.2 i).2)

theorem raw_input_readonly (q : State) (a : Fin 3 → Sym) :
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
  k := 3
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
    simp [transition, rawTransition, safe_stay]
  input_readonly := by
    intro q a
    change (safeStep (a 0) ((rawTransition q a).2 0).1 ((rawTransition q a).2 0).2).1 = a 0
    rw [raw_input_readonly]
    exact safe_write_self _ _

end IntMul.TapeAdder


