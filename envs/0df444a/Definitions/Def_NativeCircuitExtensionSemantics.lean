-- Prove2me | Definitions.Def_NativeCircuitExtensionSemantics
-- name    : NativeCircuitExtensionSemantics
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-27T05:54:41.294814+00:00
-- url     : https://prove2.me/theorems/cd05cde5-6a0a-41bf-9d4e-9d0ab34c7a56
-- title:
--   Gate-list semantics for prefix extension on native truth tables
-- statement:
--   Finite circuits extend a list of available wires one gate at a time. An address is interpreted most-significant-bit first. A candidate extension agrees with the old circuit at all addresses before the cut and yields the requested bit at the cut.
-- source:
--   Native gate-list conventions and prefix extension for the Minimum Circuit Size Problem.

import Mathlib

set_option autoImplicit false

namespace PvsNP

abbrev Str := List Bool

namespace SuccinctCircuits

/-- Opcode and two operand addresses. -/
abbrev Gate := ℕ × ℕ × ℕ

/-- Constants, NOT, AND, OR, and copy. Out-of-range reads are total. -/
def gateValue (g : Gate) (w : Str) : Bool :=
  let a := w[g.2.1]?.getD false
  let b := w[g.2.2]?.getD false
  if g.1 = 0 then false
  else if g.1 = 1 then true
  else if g.1 = 2 then !a
  else if g.1 = 3 then a && b
  else if g.1 = 4 then a || b
  else a

private def appendGate (x : Str × Gate) : Str := gateValue x.2 x.1 :: x.1

/-- All inputs and derived wires, with the most recent result first. -/
def evalRegisters (g : List Gate) (w : Str) : Str :=
  g.foldl (fun bits next => appendGate (bits, next)) w

/-- The newest wire is the default single circuit output. -/
def eval (g : List Gate) (w : Str) : Bool := (evalRegisters g w).head?.getD false

end SuccinctCircuits

namespace McspPadding

def indexAssignment (n : ℕ) (i : Fin (2^n)) (j : Fin n) : Bool :=
  i.val.testBit (n-1-j.val)

end McspPadding

namespace McspCandidateAgreement

open McspPadding SuccinctCircuits

def valueAt {n : ℕ} (g : List Gate) (i : Fin (2^n)) : Bool :=
  eval g (List.ofFn (indexAssignment n i))

/-- Checks the concrete proposed circuit, including its value at the newly read address. -/
def validUpdate {n : ℕ} (old candidate : List Gate) (cut : Fin (2^n)) (b : Bool) : Prop :=
  (∀ i : Fin (2^n), i.val < cut.val → valueAt candidate i = valueAt old i) ∧
    valueAt candidate cut = b

end McspCandidateAgreement

end PvsNP


