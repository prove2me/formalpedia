-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PFibreMahlerForms
-- name    : GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PFibreMahlerForms
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T09:35:57.77484+00:00
-- url     : https://prove2.me/theorems/fd4dce98-344b-5aa0-9abf-bd411d5dc481
-- title:
--   PFibre Mahler Forms
-- statement:
--   Definitions and structural lemmas for PFibre Mahler Forms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PFibreMahlerForms.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PDiagonalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
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
open MvPolynomial NumberField TensorProduct ComplexAt
noncomputable section
namespace FibreMahlerForms
section Dual
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι]
end Dual
section Mahler
variable {d : ℕ}
end Mahler
section Fibre
variable {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (𝓞 F) W]
  [Module.Finite (𝓞 F) W] [Module.Projective (𝓞 F) W]
variable {K : Type} [Field K] [NumberField K] [Algebra F K]
def archLin (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K) :
    FibreSpace h (τ.comp (algebraMap F K)) →ₗ[ℂ] ℂ where
  toFun ξ := (ofComplex _).symm (archFunctional τ yv ((FibreSpace.equiv h _).symm ξ))
  map_add' x y := by simp only [map_add]
  map_smul' c x := by
    rw [map_smul]
    generalize (FibreSpace.equiv h _).symm x = y
    induction y using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero, RingHom.id_apply]
    | tmul z e =>
      simp only [smul_tmul', archFunctional, TensorProduct.lift.tmul, LinearMap.mk₂_apply,
        complex_smul_def, map_mul, AlgEquiv.symm_apply_apply, RingHom.id_apply, smul_eq_mul,
        mul_assoc]
    | add x y hx hy =>
      simp only [smul_add, map_add, hx, hy, RingHom.id_apply, smul_eq_mul, mul_add]
end Fibre
end FibreMahlerForms
end
end GroundTheory.Heights₂.Heights


