-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_FeynmanKacRealResolventCoreCleanV2
-- name    : MarkovProcess_V3HRepair_FeynmanKacRealResolventCoreCleanV2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T10:19:47.910289+00:00
-- url     : https://prove2.me/theorems/f0e33921-87fc-49d8-a17e-cce2ace6e770
-- title:
--   Verified MarkovProcess source repair: FeynmanKacRealResolventCoreCleanV2
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess FeynmanKacRealResolventCoreCleanV2 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.FeynmanKacRealResolventCoreCleanV2 source SHA-256 b66a4abab3f56a49070416add48e7067d1c9b66f578e4f5cba2eed11e88c9f96. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacRealResolvent_20f8c260
import Definitions.Def_MarkovProcess_V3HRepair_FeynmanKacFunctionalCoreCleanV1

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [CompleteSpace alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

omit [LocallyCompactSpace alpha] in
/-- Feynman--Kac operators are real homogeneous. -/
theorem IsConservative.feynmanKac_smul_apply (q : alpha → ℝ) (t : NNReal) (a : ℝ)
    (f : alpha → ℝ) :
    IsConservative.feynmanKac P hP q t (a • f) =
      a • IsConservative.feynmanKac P hP q t f := by
  funext x
  change (∫ omega, Real.exp (-feynmanKacAdditiveFunctional q t omega) *
      (a • f) (omega t) ∂(IsConservative.continuousProcess P hP x)) =
    a • (∫ omega, Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)
      ∂(IsConservative.continuousProcess P hP x))
  rw [← integral_smul]
  apply integral_congr_ae
  exact Eventually.of_forall fun omega ↦ by
    simp only [Pi.smul_apply, smul_eq_mul]
    ring


omit [LocallyCompactSpace alpha] in
private theorem IsConservative.integrableOn_feynmanKacResolventReal_integrand
    {q : alpha → ℝ} (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y) {lam : ℝ} (hlam : 0 < lam)
    {f : alpha → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-lam * t) *
      IsConservative.feynmanKac P hP q (Real.toNNReal t) f x) (Ioi 0) := by
  apply Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hlam).mul_const D)
  · exact (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.mul
      ((IsConservative.measurable_feynmanKac_joint P hP hq hf).comp
        (measurable_real_toNNReal.prodMk measurable_const))).stronglyMeasurable
      ).aestronglyMeasurable.restrict
  · exact Eventually.of_forall fun t ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (IsConservative.norm_feynmanKac_le P hP hq0 (Real.toNNReal t) hfD x)
        (Real.exp_pos _).le

omit [LocallyCompactSpace alpha] in
/-- The real Feynman--Kac resolvent of a bounded measurable observable is measurable in the
starting point. -/
theorem IsConservative.measurable_feynmanKacResolventReal {q : alpha → ℝ}
    (hq : Measurable q) (lam : ℝ) {f : alpha → ℝ} (hf : Measurable f) :
    Measurable (IsConservative.feynmanKacResolventReal P hP q lam f) := by
  have hjoint : StronglyMeasurable fun p : ℝ × alpha ↦
      Real.exp (-lam * p.1) *
        IsConservative.feynmanKac P hP q (Real.toNNReal p.1) f p.2 :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
      measurable_fst).mul
      ((IsConservative.measurable_feynmanKac_joint P hP hq hf).comp
        ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
      ) |>.stronglyMeasurable
  exact (hjoint.integral_prod_left' (μ := volume.restrict (Ioi 0))).measurable

omit [LocallyCompactSpace alpha] in
/-- The real Feynman--Kac resolvent is additive on bounded measurable observables. -/
theorem IsConservative.feynmanKacResolventReal_add {q : alpha → ℝ}
    (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y) {lam : ℝ} (hlam : 0 < lam)
    {f g : alpha → ℝ} (hf : Measurable f) (hg : Measurable g) {D E : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (hgE : ∀ y, |g y| ≤ E) :
    IsConservative.feynmanKacResolventReal P hP q lam (f + g) =
      IsConservative.feynmanKacResolventReal P hP q lam f +
        IsConservative.feynmanKacResolventReal P hP q lam g := by
  funext x
  unfold IsConservative.feynmanKacResolventReal
  change (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      IsConservative.feynmanKac P hP q (Real.toNNReal t) (f + g) x) =
    (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      IsConservative.feynmanKac P hP q (Real.toNNReal t) f x) +
    ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      IsConservative.feynmanKac P hP q (Real.toNNReal t) g x
  rw [← integral_add
    (IsConservative.integrableOn_feynmanKacResolventReal_integrand
      P hP hq hq0 hlam hf hfD x)
    (IsConservative.integrableOn_feynmanKacResolventReal_integrand
      P hP hq hq0 hlam hg hgE x)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  dsimp only
  rw [congrFun (IsConservative.feynmanKac_add_apply P hP hq hq0
    (Real.toNNReal t) hf hg hfD hgE) x]
  simp only [Pi.add_apply]
  ring

omit [LocallyCompactSpace alpha] in
/-- The real Feynman--Kac resolvent is real homogeneous. -/
theorem IsConservative.feynmanKacResolventReal_smul (q : alpha → ℝ) (lam a : ℝ)
    (f : alpha → ℝ) :
    IsConservative.feynmanKacResolventReal P hP q lam (a • f) =
      a • IsConservative.feynmanKacResolventReal P hP q lam f := by
  funext x
  unfold IsConservative.feynmanKacResolventReal
  change (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      IsConservative.feynmanKac P hP q (Real.toNNReal t) (a • f) x) =
    a • (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      IsConservative.feynmanKac P hP q (Real.toNNReal t) f x)
  rw [← integral_smul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  dsimp only
  rw [congrFun (IsConservative.feynmanKac_smul_apply P hP q
    (Real.toNNReal t) a f) x]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

omit [LocallyCompactSpace alpha] in
/-- The uniform bound for the real Feynman--Kac resolvent at a positive shift. -/
theorem IsConservative.norm_feynmanKacResolventReal_le {q : alpha → ℝ}
    (hq0 : ∀ y, 0 ≤ q y) {lam : ℝ} (hlam : 0 < lam)
    {f : alpha → ℝ} {D : ℝ} (hfD : ∀ y, |f y| ≤ D)
    (x : alpha) : |IsConservative.feynmanKacResolventReal P hP q lam f x| ≤ D / lam := by
  rw [← Real.norm_eq_abs]
  unfold IsConservative.feynmanKacResolventReal
  calc
    ‖∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
        IsConservative.feynmanKac P hP q (Real.toNNReal t) f x‖ ≤
        ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * D := by
      apply norm_integral_le_of_norm_le
        ((exp_neg_integrableOn_Ioi 0 hlam).mul_const D)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (IsConservative.norm_feynmanKac_le P hP hq0 (Real.toNNReal t) hfD x)
        (Real.exp_pos _).le
    _ = D / lam := by
      rw [integral_mul_const,
        Semigroup.StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero hlam]
      field_simp

omit [LocallyCompactSpace alpha] in
/-- For a bounded nonnegative real observable, applying `ENNReal.ofReal` to the real
Feynman--Kac resolvent gives the extended-real Feynman--Kac resolvent. -/
theorem IsConservative.ofReal_feynmanKacResolventReal_eq_feynmanKacResolvent
    {q : alpha → ℝ} (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y)
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} (hf : Measurable f)
    (hf0 : ∀ y, 0 ≤ f y) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    ENNReal.ofReal (IsConservative.feynmanKacResolventReal P hP q lam f x) =
      IsConservative.feynmanKacResolvent P hP q lam
        (fun y ↦ ENNReal.ofReal (f y)) x := by
  have hint := IsConservative.integrableOn_feynmanKacResolventReal_integrand
    P hP hq hq0 hlam hf hfD x
  rw [IsConservative.feynmanKacResolventReal,
    ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun t ↦ mul_nonneg (Real.exp_pos _).le
        (IsConservative.feynmanKac_nonneg P hP hf0 x))]
  unfold IsConservative.feynmanKacResolvent
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  dsimp only
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
    IsConservative.ofReal_feynmanKac_eq_feynmanKacENNReal P hP hq hq0
      (Real.toNNReal t) hf hf0 (fun y ↦ (le_abs_self (f y)).trans (hfD y)) x]

end
end MarkovProcess.SubMarkovKernelSemigroup
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsConservative.feynmanKacResolventReal_add
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsConservative.norm_feynmanKacResolventReal_le
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsConservative.ofReal_feynmanKacResolventReal_eq_feynmanKacResolvent


