-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialAbelCode_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialAbelCode_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:34:41.55846+00:00
-- url     : https://prove2.me/theorems/0fc2e09d-cbc2-4d7d-be3c-568ee56704bb
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialAbelCode source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialAbelCode

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialAbelCode
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13AbelFiberTwoModel_p0

import Mathlib.Data.ZMod.Basic

import Mathlib.Tactic

set_option autoImplicit false




open scoped Sym2

open MazurProof.N13AbelFiberTwoModel
open MazurProof.N13SymmetricSquareTwo

namespace MazurProof.N13SpecialAbelCode

noncomputable section

abbrev Code : Type :=
  ZMod 19

abbrev EffectiveDivisorTwo : Type :=
  N13SymmetricSquareTwo.EffectiveDivisorTwo

/-- The three hyperelliptic base fibres receive amplitudes 1, 7, 8. -/
def baseAmplitude : BasePoint → Code
  | Sum.inl k => match k with
    | 0 => 1
    | 1 => 7
  | Sum.inr _ => 8

/-- The two sheets over a base point receive opposite codes. -/
def pointCode (P : N13AbelFiberTwoModel.CurvePoint) : Code :=
  let (B, z) := N13AbelFiberTwoModel.curvePointEquiv P
  if z = 0 then baseAmplitude B else -(baseAmplitude B)

/-- Code an unordered degree-two divisor by adding its two point codes. -/
def divisorCode : EffectiveDivisorTwo → Code :=
  Sym2.lift
    ⟨fun P Q => pointCode P + pointCode Q,
     fun P Q => by simp [add_comm]⟩

@[simp] theorem divisorCode_mk
    (P Q : N13AbelFiberTwoModel.CurvePoint) :
    divisorCode s(P, Q) = pointCode P + pointCode Q := by
  rfl

/-- First lemma: every member of the canonical hyperelliptic pencil has
code zero. The two sheets have opposite point codes. -/
@[simp] theorem divisorCode_canonicalDivisor
    (B : BasePoint) :
    divisorCode (canonicalDivisor B) = 0 := by
  simp [divisorCode, pointCode, N13AbelFiberTwoModel.curvePointEquiv, canonicalDivisor]
  cases B <;> simp [baseAmplitude]

/-- Second lemma: the explicit code is constant on every AbelRel class. -/
theorem divisorCode_eq_of_abelRel
    {D E : EffectiveDivisorTwo}
    (h : AbelRel D E) :
    divisorCode D = divisorCode E := by
  -- The AbelRel is D = E or both are canonical
  rcases h with rfl | ⟨hD, hE⟩
  · rfl
  · -- Both D and E are canonical divisors, so both have code 0
    have hD0 : divisorCode D = 0 := by
      obtain ⟨bD, rfl⟩ := hD
      exact divisorCode_canonicalDivisor bD
    have hE0 : divisorCode E = 0 := by
      obtain ⟨bE, rfl⟩ := hE
      exact divisorCode_canonicalDivisor bE
    rw [hD0, hE0]

end

end MazurProof.N13SpecialAbelCode


