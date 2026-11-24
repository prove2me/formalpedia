-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T18:33:15.793814+00:00
-- url     : https://prove2.me/theorems/c4d16d0e-9026-46c4-9147-f659261553e8
-- title:
--   Flag Integral Real Eq Mul Dd Const
-- statement:
--   Definitions and structural lemmas for Flag Integral Real Eq Mul Dd Const, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
def flagIntegralReal (f N : ℕ) : MvPolynomial (Fin f × Fin N) ℝ →ₗ[ℝ] ℝ where
  toFun G := ∑ α ∈ (blockVandermonde f N).support,
    coeff α G * ((coeff α (blockVandermonde f N) : ℚ) : ℝ) * α.prod (fun _ e => (e.factorial : ℝ))
  map_add' G H := by simp only [coeff_add, add_mul, sum_add_distrib]
  map_smul' c G := by simp only [coeff_smul, smul_eq_mul, RingHom.id_apply, mul_sum, mul_assoc]
namespace FlagEq
def antisym (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) : IndefiniteRowSideFullHecke.RestTerms.Roots f j k :=
  ∑ w : Fin f → Equiv.Perm (Fin (j + k)),
    ((permSign f (j + k) w : ℤ) : ℝ) • rename (Equiv.prodCongrRight w) G
end FlagEq
end
end GroundTheory.Heights₂.Heights.RestTerms


