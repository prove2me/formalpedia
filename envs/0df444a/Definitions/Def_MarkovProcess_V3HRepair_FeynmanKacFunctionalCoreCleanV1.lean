-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_FeynmanKacFunctionalCoreCleanV1
-- name    : MarkovProcess_V3HRepair_FeynmanKacFunctionalCoreCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T10:03:25.299688+00:00
-- url     : https://prove2.me/theorems/a6639c74-4f49-40bd-92bf-8291955e184a
-- title:
--   Verified MarkovProcess source repair: FeynmanKacFunctionalCoreCleanV1
-- statement:
--   Strong measurability, nonnegativity and extended-real integral identities for Feynman-Kac additive functionals and kernels.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream commit 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.FeynmanKacFunctionalCoreCleanV1 SHA-256 b40a51827f6f41865beec949d4c209842b7d8d15d7a49f4224d2ccd36c776066. Only repaired import paths were translated to the published Definitions.Def_MarkovProcess_V3HRepair_* module names.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacFunctional_cc8a1986
import Definitions.Def_MarkovProcess_V3HRepair_FeynmanKacJointMeasurableCleanV3

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
variable [SecondCountableTopology alpha]

theorem stronglyMeasurable_feynmanKacAdditiveFunctional {q : alpha → ℝ}
    (hq : Measurable q) (t : NNReal) :
    StronglyMeasurable (feynmanKacAdditiveFunctional q t) := by
  have hpair : Measurable (fun omega : ContinuousPath alpha => (t, omega)) :=
    measurable_const.prodMk measurable_id
  simpa only [Function.comp_def] using
    (stronglyMeasurable_feynmanKacAdditiveFunctional_joint hq).comp_measurable hpair

omit [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] in
/-- The accumulated potential is nonnegative. -/
theorem feynmanKacAdditiveFunctional_nonneg {q : alpha → ℝ} (hq0 : ∀ y, 0 ≤ q y)
    (t : NNReal) (omega : ContinuousPath alpha) :
    0 ≤ feynmanKacAdditiveFunctional q t omega := by
  rw [feynmanKacAdditiveFunctional_apply]
  exact intervalIntegral.integral_nonneg t.coe_nonneg fun s _ ↦ hq0 _

variable [CompleteSpace alpha] [Nonempty alpha] [LocallyCompactSpace alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

omit [LocallyCompactSpace alpha] in
/-- The Feynman--Kac operator preserves nonnegativity. -/
theorem IsConservative.feynmanKac_nonneg {q : alpha → ℝ} {t : NNReal}
    {f : alpha → ℝ} (hf0 : ∀ y, 0 ≤ f y) (x : alpha) :
    0 ≤ IsConservative.feynmanKac P hP q t f x := by
  exact integral_nonneg fun omega ↦ mul_nonneg (Real.exp_pos _).le (hf0 _)

omit [LocallyCompactSpace alpha] in
/-- The extended-real Feynman--Kac operator is unfolded as a path integral. -/
theorem IsConservative.feynmanKacENNReal_apply (q : alpha → ℝ) (t : NNReal)
    (f : alpha → ℝ≥0∞) (x : alpha) :
    IsConservative.feynmanKacENNReal P hP q t f x =
      ∫⁻ omega, ENNReal.ofReal (Real.exp (-feynmanKacAdditiveFunctional q t omega)) *
        f (omega t) ∂(IsConservative.continuousProcess P hP x) :=
  rfl

omit [LocallyCompactSpace alpha] in
/-- For nonnegative bounded real observables, the two versions of the Feynman--Kac operator agree
after applying `ENNReal.ofReal`. -/
theorem IsConservative.ofReal_feynmanKac_eq_feynmanKacENNReal {q : alpha → ℝ}
    (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y) (t : NNReal) {f : alpha → ℝ} (hf : Measurable f)
    (hf0 : ∀ y, 0 ≤ f y) {D : ℝ} (hfD : ∀ y, f y ≤ D) (x : alpha) :
    ENNReal.ofReal (IsConservative.feynmanKac P hP q t f x) =
      IsConservative.feynmanKacENNReal P hP q t (fun y ↦ ENNReal.ofReal (f y)) x := by
  let g : ContinuousPath alpha → ℝ := fun omega ↦
    Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)
  have hg : Integrable g (IsConservative.continuousProcess P hP x) := by
    refine Integrable.of_bound ?_ D (Eventually.of_forall fun omega ↦ ?_)
    · exact ((((stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.neg.exp).mul
        (hf.comp (ContinuousPath.measurable_coordinateProcess
          (alpha := alpha) t))).stronglyMeasurable
          ).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hf0 _))]
      exact (mul_le_mul_of_nonneg_right
        ((Real.exp_le_one_iff).mpr
          (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 t omega))) (hf0 _)).trans
        (by simpa only [one_mul] using hfD _)
  rw [IsConservative.feynmanKac_apply, IsConservative.feynmanKacENNReal_apply,
    ofReal_integral_eq_lintegral_ofReal hg
      (Eventually.of_forall fun omega ↦ mul_nonneg (Real.exp_pos _).le (hf0 _))]
  refine lintegral_congr fun omega ↦ ?_
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]

omit [LocallyCompactSpace alpha] in
/-- The path integrand defining a Feynman--Kac operator is integrable for a bounded observable
and a nonnegative potential. -/
theorem IsConservative.integrable_feynmanKac_integrand {q : alpha → ℝ}
    (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y) (t : NNReal) {f : alpha → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    Integrable (fun omega : ContinuousPath alpha ↦
      Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t))
      (IsConservative.continuousProcess P hP x) := by
  exact Integrable.of_bound
    (((((stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.neg.exp).mul
      (hf.comp (ContinuousPath.measurable_coordinateProcess (alpha := alpha) t))
      ).stronglyMeasurable).aestronglyMeasurable) D (Eventually.of_forall fun omega ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-feynmanKacAdditiveFunctional q t omega) * |f (omega t)| ≤
            1 * |f (omega t)| := mul_le_mul_of_nonneg_right
              ((Real.exp_le_one_iff).mpr
                (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 t omega)))
              (abs_nonneg _)
        _ ≤ D := by simpa only [one_mul] using hfD _)

omit [LocallyCompactSpace alpha] in
/-- Feynman--Kac operators are additive on bounded measurable real observables. -/
theorem IsConservative.feynmanKac_add_apply {q : alpha → ℝ} (hq : Measurable q)
    (hq0 : ∀ y, 0 ≤ q y) (t : NNReal) {f g : alpha → ℝ}
    (hf : Measurable f) (hg : Measurable g) {D E : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (hgE : ∀ y, |g y| ≤ E) :
    IsConservative.feynmanKac P hP q t (f + g) =
      IsConservative.feynmanKac P hP q t f + IsConservative.feynmanKac P hP q t g := by
  funext x
  change (∫ omega, Real.exp (-feynmanKacAdditiveFunctional q t omega) *
      (f + g) (omega t) ∂(IsConservative.continuousProcess P hP x)) =
    (∫ omega, Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)
      ∂(IsConservative.continuousProcess P hP x)) +
    ∫ omega, Real.exp (-feynmanKacAdditiveFunctional q t omega) * g (omega t)
      ∂(IsConservative.continuousProcess P hP x)
  rw [← integral_add
      (IsConservative.integrable_feynmanKac_integrand P hP hq hq0 t hf hfD x)
      (IsConservative.integrable_feynmanKac_integrand P hP hq hq0 t hg hgE x)]
  apply integral_congr_ae
  exact Eventually.of_forall fun omega ↦ by
    simp only [Pi.add_apply]
    ring

omit [LocallyCompactSpace alpha] in
/-- A Feynman--Kac operator contracts the uniform bound of a bounded observable when
the potential is nonnegative. -/
theorem IsConservative.norm_feynmanKac_le {q : alpha → ℝ} (hq0 : ∀ y, 0 ≤ q y)
    (t : NNReal) {f : alpha → ℝ} {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    |IsConservative.feynmanKac P hP q t f x| ≤ D := by
  rw [← Real.norm_eq_abs]
  calc
    ‖IsConservative.feynmanKac P hP q t f x‖ ≤ ∫ _omega, D
        ∂(IsConservative.continuousProcess P hP x) := by
      rw [IsConservative.feynmanKac_apply]
      apply norm_integral_le_of_norm_le (integrable_const D)
      exact Eventually.of_forall fun omega ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact (mul_le_mul_of_nonneg_right
          ((Real.exp_le_one_iff).mpr
            (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 t omega)))
          (abs_nonneg _)).trans (by simpa only [one_mul] using hfD _)
    _ = D := by simp only [integral_const, probReal_univ, one_smul]

end
end MarkovProcess.SubMarkovKernelSemigroup
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsConservative.feynmanKac_add_apply
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsConservative.norm_feynmanKac_le
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsConservative.ofReal_feynmanKac_eq_feynmanKacENNReal


