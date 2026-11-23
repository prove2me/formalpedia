-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevDuality
-- name    : GroundTheory_AutomorphicForms_PartialDifferential_SobolevDuality
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:18.943819+00:00
-- url     : https://prove2.me/theorems/b252cb69-1a3c-4b48-add1-c02ee60ead4a
-- title:
--   Sobolev Duality
-- statement:
--   Definitions and structural lemmas for Sobolev Duality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevDuality.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_P2M_GroundTheory_Automorphic_Sobolev_SobolevSpace_bessel___apply_2484824798c0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM


set_option autoImplicit false
namespace GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
section Duality
variable {s : ℝ}
theorem star_add_lpTwo (f g : Lp ℂ 2 (volume : Measure E)) :
    (star (f + g) : Lp ℂ 2 (volume : Measure E)) = star f + star g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (f + g), Lp.coeFn_star f, Lp.coeFn_star g,
    Lp.coeFn_add (star f) (star g), Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h2, h3]
  simp only [Pi.star_apply]
  rw [h5, Pi.add_apply, star_add]
theorem star_smul_lpTwo (c : ℂ) (f : Lp ℂ 2 (volume : Measure E)) :
    (star (c • f) : Lp ℂ 2 (volume : Measure E)) = (starRingEnd ℂ c) • star f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (c • f), Lp.coeFn_star f, Lp.coeFn_smul (starRingEnd ℂ c) (star f),
    Lp.coeFn_smul c f] with x h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, h2]
  simp [h4]
theorem norm_star_lpTwo (f : Lp ℂ 2 (volume : Measure E)) :
    ‖(star f : Lp ℂ 2 (volume : Measure E))‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star f)]
  congr 1
  apply eLpNorm_congr_norm_ae
  exact ae_of_all _ fun x ↦ by simp
def dualPairing (v : SobolevSpace E ℂ (-s)) : StrongDual ℂ (SobolevSpace E ℂ s) :=
  (innerSL ℂ (star (SobolevSpace.bessel (-s) v) : Lp ℂ 2 (volume : Measure E))).comp
    ((SobolevSpace.besselₗᵢ (E := E) (F := ℂ) s) : SobolevSpace E ℂ s →L[ℂ] Lp ℂ 2 (volume : Measure E))
theorem dualPairing_apply' (v : SobolevSpace E ℂ (-s)) (u : SobolevSpace E ℂ s) :
    dualPairing v u = inner ℂ (star (SobolevSpace.bessel (-s) v) : Lp ℂ 2 (volume : Measure E))
      (SobolevSpace.bessel s u) := rfl
theorem norm_dualPairing (v : SobolevSpace E ℂ (-s)) : ‖dualPairing (s := s) v‖ = ‖v‖ := by
  rw [dualPairing, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv, innerSL_apply_norm,
    norm_star_lpTwo]
  rfl
def dualPairingₗᵢ : SobolevSpace E ℂ (-s) →ₗᵢ[ℂ] StrongDual ℂ (SobolevSpace E ℂ s) where
  toFun := dualPairing
  map_add' v w := by
    ext u
    rw [ContinuousLinearMap.add_apply, dualPairing_apply', dualPairing_apply',
      dualPairing_apply', map_add, star_add_lpTwo, inner_add_left]
  map_smul' c v := by
    ext u
    rw [ContinuousLinearMap.smul_apply, dualPairing_apply', dualPairing_apply', map_smul,
      star_smul_lpTwo, inner_smul_left, Complex.conj_conj, RingHom.id_apply, smul_eq_mul]
  norm_map' v := norm_dualPairing v
theorem dualPairing_surjective :
    Function.Surjective (dualPairing : SobolevSpace E ℂ (-s) → StrongDual ℂ (SobolevSpace E ℂ s)) := by
  intro ℓ
  set L : StrongDual ℂ (Lp ℂ 2 (volume : Measure E)) :=
    ℓ.comp (SobolevSpace.besselₗᵢ s).symm.toLinearIsometry.toContinuousLinearMap
  set y := (InnerProductSpace.toDual ℂ (Lp ℂ 2 (volume : Measure E))).symm L
  refine ⟨(SobolevSpace.besselₗᵢ (-s)).symm (star y), ?_⟩
  ext u
  have hy : ∀ g, inner ℂ y g = L g := fun g ↦ by
    rw [← InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [dualPairing_apply', ← SobolevSpace.besselₗᵢ_apply, LinearIsometryEquiv.apply_symm_apply,
    star_star, hy]
  simp only [L, ContinuousLinearMap.comp_apply]
  rw [← SobolevSpace.besselₗᵢ_apply]
  simp
def dualEquiv : SobolevSpace E ℂ (-s) ≃ₗᵢ[ℂ] StrongDual ℂ (SobolevSpace E ℂ s) :=
  LinearIsometryEquiv.ofSurjective dualPairingₗᵢ dualPairing_surjective
end Duality
end
end GroundTheory.Automorphic.Sobolev


