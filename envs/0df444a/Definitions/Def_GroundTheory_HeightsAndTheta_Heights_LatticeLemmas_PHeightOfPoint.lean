-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHeightOfPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHeightOfPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:31.790474+00:00
-- url     : https://prove2.me/theorems/c9b6ff59-532f-4073-ac3f-d79b788a6438
-- title:
--   PHeight Of Point
-- statement:
--   Definitions and structural lemmas for PHeight Of Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHeightOfPoint.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
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
open MvPolynomial NumberField ComplexAt TensorProduct
noncomputable section
namespace HeightOfPointAlt
variable {K : Type*} [Field K] [NumberField K]
variable {F : Type*} [Field F] [NumberField F] [Algebra F K]
variable {W : Type*} [AddCommGroup W] [Module (𝓞 F) W] [Module.Finite (𝓞 F) W]
  [Module.Projective (𝓞 F) W]
def archLinear (τ : K →+* ℂ) (yv : DualVec F W K) :
    Fibre (τ.comp (algebraMap F K)) W →ₗ[ℂ] ComplexAt (τ.comp (algebraMap F K)) where
  toFun := archFunctional τ yv
  map_add' := map_add _
  map_smul' c t := by
    induction t using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul z e =>
      rw [TensorProduct.smul_tmul', RingHom.id_apply]
      simp only [archFunctional, TensorProduct.lift.tmul, LinearMap.mk₂_apply]
      exact smul_mul_assoc c z _
    | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]
end HeightOfPointAlt
open HeightOfPointAlt
end
end GroundTheory.Heights₂.Heights


