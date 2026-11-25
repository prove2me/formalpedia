-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T12:41:10.085982+00:00
-- url     : https://prove2.me/theorems/5bf7a8d2-b6d4-450e-b1ba-c3faacd19a57
-- title:
--   Gelfand Ps A
-- statement:
--   Definitions and structural lemmas for Gelfand Ps A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped ContDiff
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace GPs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def mulL (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ X)
def conjLE (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1) (hBA : B * A = 1) :
    Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun z := A * z * B
  invFun z := B * z * A
  map_add' x y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by simp
  left_inv z := by
    simp only [← Matrix.mul_assoc]
    rw [hBA, Matrix.one_mul, Matrix.mul_assoc, hBA, Matrix.mul_one]
  right_inv z := by
    simp only [← Matrix.mul_assoc]
    rw [hAB, Matrix.one_mul, Matrix.mul_assoc, hAB, Matrix.mul_one]
end GPs
end ReciprocityTheory.ChartRestriction.DS.S7


