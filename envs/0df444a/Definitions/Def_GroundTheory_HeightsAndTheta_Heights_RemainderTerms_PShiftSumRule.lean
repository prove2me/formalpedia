-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PShiftSumRule
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PShiftSumRule
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:14.181735+00:00
-- url     : https://prove2.me/theorems/0880c4d6-8c55-4e25-9871-6508b52c047d
-- title:
--   PShift Sum Rule
-- statement:
--   Definitions and structural lemmas for PShift Sum Rule, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PShiftSumRule.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
namespace RestTerms
open MvPolynomial Finset
noncomputable section
namespace ShiftSumRule
def flagIntegralLinear (f N : ℕ) : RootRing f N →ₗ[ℚ] ℚ where
  toFun := flagIntegral f N
  map_add' Φ Ψ := by simp only [flagIntegral, coeff_add, add_mul, Finset.sum_add_distrib]
  map_smul' b Φ := by
    simp only [flagIntegral, coeff_smul, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]
end ShiftSumRule
end
end RestTerms
end GroundTheory.Heights₂.Heights


