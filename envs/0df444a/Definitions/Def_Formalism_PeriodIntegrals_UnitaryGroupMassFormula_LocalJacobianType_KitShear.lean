-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitShear
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitShear
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T12:33:34.610236+00:00
-- url     : https://prove2.me/theorems/dce7b75d-c776-5464-a1e4-86b22c966457
-- title:
--   Kit Shear
-- statement:
--   Definitions and structural lemmas for Kit Shear, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/KitShear.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMul
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_locallyCompact_Fv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_secondCountable_Fv
import Theorems.Thm_PI_VolStabSW_HasDens_add
import Theorems.Thm_PI_VolStabSW_HasDens_sub
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv
import Theorems.Thm_PI_VolStabSW_secondCountable_Fv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim
section Gen
variable {W : Type} [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [LocallyCompactSpace W] [SecondCountableTopology W] [T2Space W] [MeasurableSpace W] [BorelSpace W]
end Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}
theorem continuous_sigR' (σ : E →ₐ[F] E) : Continuous (sigR (Fv F v) σ) := by
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have h : ∀ x : Fv F v ⊗[F] E, sigR (Fv F v) σ x = (σ.toLinearMap.baseChange (Fv F v)) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have : (sigR (Fv F v) σ : Fv F v ⊗[F] E → Fv F v ⊗[F] E) = (σ.toLinearMap.baseChange (Fv F v)) :=
    funext h
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap _
namespace SD
variable (D : SD σ v)
theorem e_mul_f : D.e * (1 - D.e) = 0 := by
  rw [mul_sub, mul_one, D.he.eq, sub_self]
def shear {ι : Type} (τ : ι → ι) : (ι → Fv F v ⊗[F] E) ≃ₜ+ (ι → Fv F v ⊗[F] E) where
  toFun z k := z k + D.e * sigR (Fv F v) σ (z (τ k))
  invFun w k := w k - D.e * sigR (Fv F v) σ (w (τ k))
  left_inv z := by
    funext k
    simp only [map_add, map_mul, D.hσ]
    linear_combination (-(sigR (Fv F v) σ (sigR (Fv F v) σ (z (τ (τ k)))))) * D.e_mul_f
  right_inv w := by
    funext k
    simp only [map_sub, map_mul, D.hσ]
    linear_combination (-(sigR (Fv F v) σ (sigR (Fv F v) σ (w (τ (τ k)))))) * D.e_mul_f
  map_add' x y := by
    funext k
    simp only [Pi.add_apply, map_add]
    ring
  continuous_toFun := continuous_pi fun k =>
    (continuous_apply k).add (continuous_const.mul ((continuous_sigR' σ).comp (continuous_apply (τ k))))
  continuous_invFun := continuous_pi fun k =>
    (continuous_apply k).sub (continuous_const.mul ((continuous_sigR' σ).comp (continuous_apply (τ k))))
def pt (s t : Fv F v) : Fv F v ⊗[F] E := s • D.e + t • (1 - D.e)
end SD
end PI.UnitaryGroupMassFormula.LocJacTyp


