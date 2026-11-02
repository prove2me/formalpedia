-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_ResolventProofs
-- name    : MarkovProcess_V3HRepair_ResolventProofs
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T10:19:17.273196+00:00
-- url     : https://prove2.me/theorems/3d64817b-b407-48b4-9840-3d017e411ab9
-- title:
--   Verified MarkovProcess source repair: ResolventProofs
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess ResolventProofs module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.ResolventProofs source SHA-256 86f792aa2936f3fd8349761d33f38639524efbf6a905985bfb07c3e4ac90dd86. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names.

import Definitions.Def_MarkovProcess_V3H_Kernel_Resolvent_f63a7282
import Definitions.Def_MarkovProcess_V3H_Kernel_Basic_264434f5
import Definitions.Def_MarkovProcess_V3HRepair_MeasurableKernelIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup
variable {alpha : Type*} [MeasurableSpace alpha]

theorem norm_kernelIntegral_le_of_bound (P : SubMarkovKernelSemigroup alpha)
    {f : alpha → ℝ} {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (t : NNReal) (x : alpha) :
    |kernelIntegral (P t) f x| ≤ D := by
  have hD0 : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  rw [← Real.norm_eq_abs]
  let : IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  calc
    ‖kernelIntegral (P t) f x‖ ≤ ∫ _y, D ∂(P t x) := by
      apply norm_integral_le_of_norm_le (integrable_const D)
      exact Eventually.of_forall hfD
    _ ≤ D := by
      rw [integral_const, smul_eq_mul]
      apply mul_le_of_le_one_left hD0
      rw [measureReal_def, ← ENNReal.toReal_one]
      apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2
      exact (P.isSubMarkovKernel t).measure_le_one x Set.univ
theorem integrableOn_kernelResolventReal_integrand
    (P : SubMarkovKernelSemigroup alpha) {lam : ℝ} (hlam : 0 < lam)
    {f : alpha → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) f x) (Ioi 0) := by
  apply Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hlam).mul_const D)
  · exact (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.mul
      ((P.measurable_kernelIntegral hf).comp
        (measurable_real_toNNReal.prodMk measurable_const))).stronglyMeasurable
      ).aestronglyMeasurable.restrict
  · exact Eventually.of_forall fun t ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (norm_kernelIntegral_le_of_bound P hfD (Real.toNNReal t) x) (Real.exp_pos _).le

/-- The real kernel resolvent is additive on bounded measurable observables. -/
theorem kernelResolventReal_add (P : SubMarkovKernelSemigroup alpha)
    {lam : ℝ} (hlam : 0 < lam) {f g : alpha → ℝ}
    (hf : Measurable f) (hg : Measurable g) {D E : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (hgE : ∀ y, |g y| ≤ E) :
    P.kernelResolventReal lam (f + g) =
      P.kernelResolventReal lam f + P.kernelResolventReal lam g := by
  funext x
  unfold kernelResolventReal
  change (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) (f + g) x) =
    (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) f x) +
    ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) g x
  rw [← integral_add
    (integrableOn_kernelResolventReal_integrand P hlam hf hfD x)
    (integrableOn_kernelResolventReal_integrand P hlam hg hgE x)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  let : IsFiniteKernel (P (Real.toNNReal t)) :=
    (P.isSubMarkovKernel (Real.toNNReal t)).isFiniteKernel
  have hfint : Integrable f (P (Real.toNNReal t) x) :=
    Integrable.of_bound hf.stronglyMeasurable.aestronglyMeasurable D
      (Eventually.of_forall hfD)
  have hgint : Integrable g (P (Real.toNNReal t) x) :=
    Integrable.of_bound hg.stronglyMeasurable.aestronglyMeasurable E
      (Eventually.of_forall hgE)
  have hinner : kernelIntegral (P (Real.toNNReal t)) (f + g) x =
      kernelIntegral (P (Real.toNNReal t)) f x +
        kernelIntegral (P (Real.toNNReal t)) g x := by
    unfold kernelIntegral
    simpa only [Pi.add_apply] using integral_add hfint hgint
  dsimp only
  rw [hinner]
  ring
theorem norm_kernelResolventReal_le (P : SubMarkovKernelSemigroup alpha)
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} {D : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    |P.kernelResolventReal lam f x| ≤ D / lam := by
  rw [← Real.norm_eq_abs]
  unfold kernelResolventReal
  calc
    ‖∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
        kernelIntegral (P (Real.toNNReal t)) f x‖ ≤
        ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * D := by
      apply norm_integral_le_of_norm_le
        ((exp_neg_integrableOn_Ioi 0 hlam).mul_const D)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (norm_kernelIntegral_le_of_bound P hfD (Real.toNNReal t) x) (Real.exp_pos _).le
    _ = D / lam := by
      rw [integral_mul_const, integral_exp_mul_Ioi (neg_neg_of_pos hlam) 0]
      simp only [mul_zero, Real.exp_zero]
      field_simp

end MarkovProcess.SubMarkovKernelSemigroup


