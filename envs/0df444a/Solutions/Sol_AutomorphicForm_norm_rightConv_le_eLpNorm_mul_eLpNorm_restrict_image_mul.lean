-- Prove2me | solution 1 for AutomorphicForm.norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/97d301a4-f564-556c-9ef3-59b5f0612716

import Mathlib
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul

set_option autoImplicit false
open NumberField NumberField.AdelicHaar AutomorphicForm MeasureTheory

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K]
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hφ : Continuous φ) (hf : Continuous f)
    (hfs : HasCompactSupport f) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    ‖rightConv K φ f g‖ ≤
      (eLpNorm f 2 (adelicGLHaar (Fin 2) (𝓞 K) K)).toReal *
        (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict ((fun x => g * x) '' tsupport f))).toReal := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set T := tsupport f with hT
  have hTc : IsCompact T := hfs

  let F : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ := fun x => ‖φ (g * x)‖
  let G : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ := fun x => ‖f x‖
  have hφg : Continuous fun x => φ (g * x) := hφ.comp (continuous_const.mul continuous_id)
  have hFc : Continuous F := continuous_norm.comp hφg
  have hGc : Continuous G := continuous_norm.comp hf

  have hF2 : MemLp F (ENNReal.ofReal 2) (μ.restrict T) := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    refine (memLp_two_iff_integrable_sq hFc.aestronglyMeasurable).mpr ?_
    exact (hFc.pow 2).continuousOn.integrableOn_compact hTc
  have hG2 : MemLp G (ENNReal.ofReal 2) (μ.restrict T) := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    refine (memLp_two_iff_integrable_sq hGc.aestronglyMeasurable).mpr ?_
    exact (hGc.pow 2).continuousOn.integrableOn_compact hTc

  have h1 : ‖rightConv K φ f g‖ ≤ ∫ x in T, F x * G x ∂μ := by
    rw [rightConv_apply]
    show ‖∫ x, φ (g * x) * f x ∂μ‖ ≤ _
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := T) (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero])]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact norm_mul _ _

  have h2 : ∫ x in T, F x * G x ∂μ ≤ (∫ x in T, F x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (∫ x in T, G x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) (Filter.Eventually.of_forall fun _ => norm_nonneg _) hF2 hG2

  have hGint : (∫ x in T, G x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = (eLpNorm f 2 μ).toReal := by
    have hmem : MemLp f 2 μ := hf.memLp_of_hasCompactSupport hfs
    rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofReal
      (Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) _),
      ENNReal.toReal_ofNat, ← one_div]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := T) (fun x hx => by
      show ‖f x‖ ^ (2 : ℝ) = 0
      rw [image_eq_zero_of_notMem_tsupport hx, norm_zero, Real.zero_rpow two_ne_zero])]
  have hFint : (∫ x in T, F x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
      = (eLpNorm φ 2 (μ.restrict ((fun x => g * x) '' T))).toReal := by

    have hmp : MeasurePreserving (fun x : GL (Fin 2) (AdeleRing (𝓞 K) K) => g * x) μ μ := measurePreserving_mul_left μ g
    have hemb : MeasurableEmbedding (fun x : GL (Fin 2) (AdeleRing (𝓞 K) K) => g * x) :=
      (Homeomorph.mulLeft g).measurableEmbedding
    have hcv : ∫ y in (fun x => g * x) '' T, ‖φ y‖ ^ (2 : ℝ) ∂μ = ∫ x in T, F x ^ (2 : ℝ) ∂μ :=
      hmp.setIntegral_image_emb hemb (fun y => ‖φ y‖ ^ (2 : ℝ)) T
    have hTc' : IsCompact ((fun x => g * x) '' T) := hTc.image (continuous_const.mul continuous_id)
    have hmem : MemLp φ 2 (μ.restrict ((fun x => g * x) '' T)) := by
      refine (memLp_two_iff_integrable_sq_norm hφ.aestronglyMeasurable).mpr ?_
      exact ((continuous_norm.comp hφ).pow 2).continuousOn.integrableOn_compact hTc'
    rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofReal
      (Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) _),
      ENNReal.toReal_ofNat, ← one_div, hcv]
  calc ‖rightConv K φ f g‖ ≤ ∫ x in T, F x * G x ∂μ := h1
    _ ≤ (∫ x in T, F x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (∫ x in T, G x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := h2
    _ = (eLpNorm f 2 μ).toReal * (eLpNorm φ 2 (μ.restrict ((fun x => g * x) '' T))).toReal := by
        rw [hFint, hGint, mul_comm]

end S_AutomorphicForm_norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul
end P2MW
export P2MW.S_AutomorphicForm_norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul (solution)
