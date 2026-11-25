-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
-- name    : GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:34:17.432069+00:00
-- url     : https://prove2.me/theorems/59634b5e-618b-4cc0-9eba-999cc9f65a83
-- title:
--   Sobolev Rellich
-- statement:
--   Definitions and structural lemmas for Sobolev Rellich, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevRellich.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_add
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_comp_left
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_exists_norm_le_weight
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_peetre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_convolutionCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_sub
attribute [local simp] GroundTheory.Automorphic.Sobolev.dualEquiv_apply


set_option autoImplicit false
namespace GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
def cutoff (R : ℝ) : 𝓢(E, ℂ) :=
  let b : ContDiffBump (0 : E) := ⟨R.toNNReal + 1, R.toNNReal + 2, by positivity, by linarith⟩
  have h₁ : HasCompactSupport (Complex.ofRealCLM ∘ (b : E → ℝ)) := b.hasCompactSupport.comp_left rfl
  have h₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ (b : E → ℝ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  h₁.toSchwartzMap h₂
section Kernel
variable (s N : ℝ) (χ : 𝓢(E, ℂ))
def rellichKernel (p : E × E) : ℂ :=
  weight (s - N) p.1 * (𝓕 χ : 𝓢(E, ℂ)) (p.1 - p.2) * weight (-s) p.2
variable {s N}
theorem continuous_rellichKernel : Continuous (rellichKernel (E := E) s N χ) := by
  unfold rellichKernel
  have h1 := (weight_hasTemperateGrowth (E := E) (s - N)).1.continuous
  have h2 := (weight_hasTemperateGrowth (E := E) (-s)).1.continuous
  fun_prop
theorem norm_rellichKernel_sq_le (ξ η : E) :
    ‖rellichKernel s N χ (ξ, η)‖ ^ 2 ≤
      2 ^ |s| * (1 + ‖ξ‖ ^ 2) ^ (-N) *
        ((1 + ‖ξ - η‖ ^ 2) ^ |s| * ‖(𝓕 χ : 𝓢(E, ℂ)) (ξ - η)‖ ^ 2) := by
  have pξ : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  have pη : (0 : ℝ) < 1 + ‖η‖ ^ 2 := by positivity
  have hp := peetre (-s) η ξ
  rw [abs_neg, norm_sub_rev η ξ] at hp
  simp only [rellichKernel, norm_mul, norm_weight, mul_pow]
  have e1 : ((1 + ‖ξ‖ ^ 2) ^ ((s - N) / 2)) ^ 2 = (1 + ‖ξ‖ ^ 2) ^ (s - N) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul pξ.le]; congr 1; push_cast; ring
  have e2 : ((1 + ‖η‖ ^ 2) ^ (-s / 2)) ^ 2 = (1 + ‖η‖ ^ 2) ^ (-s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul pη.le]; congr 1; push_cast; ring
  rw [e1, e2]
  have e3 : (1 + ‖ξ‖ ^ 2) ^ (s - N) * (1 + ‖ξ‖ ^ 2) ^ (-s) = (1 + ‖ξ‖ ^ 2) ^ (-N) := by
    rw [← Real.rpow_add pξ]; congr 1; ring
  calc (1 + ‖ξ‖ ^ 2) ^ (s - N) * ‖(𝓕 χ : 𝓢(E, ℂ)) (ξ - η)‖ ^ 2 * (1 + ‖η‖ ^ 2) ^ (-s)
      ≤ (1 + ‖ξ‖ ^ 2) ^ (s - N) * ‖(𝓕 χ : 𝓢(E, ℂ)) (ξ - η)‖ ^ 2 *
          (2 ^ |s| * (1 + ‖ξ - η‖ ^ 2) ^ |s| * (1 + ‖ξ‖ ^ 2) ^ (-s)) := by gcongr
    _ = 2 ^ |s| * ((1 + ‖ξ‖ ^ 2) ^ (s - N) * (1 + ‖ξ‖ ^ 2) ^ (-s)) *
          ((1 + ‖ξ - η‖ ^ 2) ^ |s| * ‖(𝓕 χ : 𝓢(E, ℂ)) (ξ - η)‖ ^ 2) := by ring
    _ = _ := by rw [e3]
theorem integrable_weight_mul_norm_fourier_sq (s : ℝ) :
    Integrable (fun ζ : E ↦ (1 + ‖ζ‖ ^ 2) ^ |s| * ‖(𝓕 χ : 𝓢(E, ℂ)) ζ‖ ^ 2) (volume : Measure E) := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  obtain ⟨C, hC⟩ := exists_norm_le_weight (𝓕 χ : 𝓢(E, ℂ)) (-(n + 1) / 2 - |s|)
  have hint := (integrable_rpow_neg_one_add_norm_sq (E := E) (μ := (volume : Measure E))
    (r := n + 1) (by linarith)).const_mul (C ^ 2)
  refine hint.mono' ?_ (ae_of_all _ fun ζ ↦ ?_)
  · have hc : Continuous (fun ζ : E ↦ (1 + ‖ζ‖ ^ 2) ^ |s|) :=
      (continuous_const.add (continuous_norm.pow 2)).rpow_const
        fun ζ ↦ Or.inl (by positivity : (0 : ℝ) < 1 + ‖ζ‖ ^ 2).ne'
    exact (hc.mul ((𝓕 χ : 𝓢(E, ℂ)).continuous.norm.pow 2)).aestronglyMeasurable
  · have pζ : (0 : ℝ) < 1 + ‖ζ‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := hC ζ
    have h2 : ‖(𝓕 χ : 𝓢(E, ℂ)) ζ‖ ^ 2 ≤ (C * (1 + ‖ζ‖ ^ 2) ^ ((-(n + 1) / 2 - |s|) / 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc (1 + ‖ζ‖ ^ 2) ^ |s| * ‖(𝓕 χ : 𝓢(E, ℂ)) ζ‖ ^ 2
        ≤ (1 + ‖ζ‖ ^ 2) ^ |s| * (C * (1 + ‖ζ‖ ^ 2) ^ ((-(n + 1) / 2 - |s|) / 2)) ^ 2 := by
          gcongr
      _ = C ^ 2 * (1 + ‖ζ‖ ^ 2) ^ (-(n + 1) / 2) := by
          rw [mul_pow, ← Real.rpow_natCast ((1 + ‖ζ‖ ^ 2) ^ _), ← Real.rpow_mul pζ.le]
          rw [mul_left_comm, ← Real.rpow_add pζ]
          congr 2; push_cast; ring
theorem memLp_rellichKernel (hN : (Module.finrank ℝ E : ℝ) < 2 * N) :
    MemLp (rellichKernel s N χ) 2 ((volume : Measure E).prod volume) := by
  have hmeas := (continuous_rellichKernel (s := s) (N := N) χ).aestronglyMeasurable
    (μ := (volume : Measure E).prod volume)
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hH := integrable_weight_mul_norm_fourier_sq χ s
  have hW := integrable_rpow_neg_one_add_norm_sq (E := E) (μ := (volume : Measure E))
    (r := 2 * N) hN
  have hW' : Integrable (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ (-N)) (volume : Measure E) := by
    refine hW.congr (ae_of_all _ fun ξ ↦ ?_)
    simp only; congr 1; ring
  set H : E → ℝ := fun ζ ↦ (1 + ‖ζ‖ ^ 2) ^ |s| * ‖(𝓕 χ : 𝓢(E, ℂ)) ζ‖ ^ 2
  have hdom : Integrable (fun p : E × E ↦ 2 ^ |s| * (1 + ‖p.1‖ ^ 2) ^ (-N) * H (p.1 - p.2))
      ((volume : Measure E).prod volume) := by
    have hg := (hW'.const_mul (2 ^ |s|)).mul_prod (hH.comp_neg (μ := (volume : Measure E)))
    have hc := ((measurePreserving_prod_sub (volume : Measure E) (volume : Measure E)).integrable_comp
      hg.aestronglyMeasurable).2 hg
    refine hc.congr (ae_of_all _ fun p ↦ ?_)
    simp only [Function.comp_apply, neg_sub]
  refine hdom.mono' (hmeas.norm.pow 2) (ae_of_all _ fun p ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact norm_rellichKernel_sq_le χ p.1 p.2
end Kernel
section Identity
variable {s N : ℝ} (χ : 𝓢(E, ℂ))
def rellichOp (hN : (Module.finrank ℝ E : ℝ) < 2 * N) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  L2Kernel.kernelOp ((memLp_rellichKernel (s := s) χ hN).toLp _)
end Identity
end
end GroundTheory.Automorphic.Sobolev


