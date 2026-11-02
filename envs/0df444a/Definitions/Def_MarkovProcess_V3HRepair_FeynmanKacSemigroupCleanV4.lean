-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_FeynmanKacSemigroupCleanV4
-- name    : MarkovProcess_V3HRepair_FeynmanKacSemigroupCleanV4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T10:41:12.434556+00:00
-- url     : https://prove2.me/theorems/4e3c5743-2809-43af-8205-36c77fe516fa
-- title:
--   Verified MarkovProcess source repair: FeynmanKacSemigroupCleanV4
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess FeynmanKacSemigroupCleanV4 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.FeynmanKacSemigroupCleanV4 source SHA-256 5eb9dfadd82ed4e4f244cf9091b44faf950a53cecdec05664ffe4006680357ab. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3HRepair_FeynmanKacFunctionalCoreCleanV1
import Definitions.Def_MarkovProcess_V3HRepair_FellerConditionalCleanV5
import Definitions.Def_MarkovProcess_V3HRepair_FeynmanKacCanonicalMeasurableCleanV4

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [CompleteSpace alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]


omit [SecondCountableTopology alpha] in
/-- A bounded measurable potential is interval integrable along every continuous path. -/
private theorem intervalIntegrable_potential_path {q : alpha → ℝ} (hq : Measurable q)
    {C : ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    (omega : ContinuousPath alpha) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ ↦ q (omega (Real.toNNReal s))) volume a b := by
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound (by simpa only [uIoc] using
      (measure_Ioc_lt_top : volume (Ioc (min a b) (max a b)) < ∞))
    (((hq.comp (omega.continuous.measurable.comp measurable_real_toNNReal)).stronglyMeasurable
      ).aestronglyMeasurable.restrict) C ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s _
  rw [Real.norm_eq_abs, abs_of_nonneg (hq0 _)]
  exact hqC _


omit [SecondCountableTopology alpha] in
/-- Accumulated potentials add under deterministic path shifts. -/
theorem feynmanKacAdditiveFunctional_add {q : alpha → ℝ} (hq : Measurable q)
    {C : ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    (s t : NNReal) (omega : ContinuousPath alpha) :
    feynmanKacAdditiveFunctional q (s + t) omega =
      feynmanKacAdditiveFunctional q s omega +
        feynmanKacAdditiveFunctional q t (ContinuousPath.shift s omega) := by
  let g : ℝ → ℝ := fun u ↦ q (omega (Real.toNNReal u))
  have hshift : (∫ u in (0 : ℝ)..(t : ℝ), q (omega (s + Real.toNNReal u))) =
      ∫ v in (s : ℝ)..((s + t : NNReal) : ℝ), g v := by
    have hcongr : (∫ u in (0 : ℝ)..(t : ℝ), q (omega (s + Real.toNNReal u))) =
        ∫ u in (0 : ℝ)..(t : ℝ), g (u + s) := by
      refine intervalIntegral.integral_congr fun u hu ↦ ?_
      have hu0 : 0 ≤ u := by
        rw [uIcc_of_le t.coe_nonneg] at hu
        exact hu.1
      have hcoe : Real.toNNReal (u + s) = s + Real.toNNReal u := by
        apply NNReal.coe_injective
        rw [NNReal.coe_add, Real.coe_toNNReal u hu0,
          Real.coe_toNNReal _ (add_nonneg hu0 s.coe_nonneg)]
        ring
      simp only [g]
      rw [hcoe]
    rw [hcongr, intervalIntegral.integral_comp_add_right g (s : ℝ), zero_add]
    congr 1
    simp only [NNReal.coe_add, add_comm]
  have hsplit : (∫ v in (0 : ℝ)..(s : ℝ), g v) +
      (∫ v in (s : ℝ)..((s + t : NNReal) : ℝ), g v) =
        ∫ v in (0 : ℝ)..((s + t : NNReal) : ℝ), g v :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_potential_path hq hq0 hqC omega 0 s)
      (intervalIntegrable_potential_path hq hq0 hqC omega s (s + t))
  simp only [feynmanKacAdditiveFunctional_apply, ContinuousPath.shift_apply]
  change (∫ v in (0 : ℝ)..((s + t : NNReal) : ℝ), g v) =
    (∫ v in (0 : ℝ)..(s : ℝ), g v) +
      ∫ u in (0 : ℝ)..(t : ℝ), q (omega (s + Real.toNNReal u))
  rw [hshift]
  exact hsplit.symm


omit [LocallyCompactSpace alpha] in
/-- The Feynman--Kac operator of a bounded measurable function is measurable in the starting
point. -/
theorem IsConservative.measurable_feynmanKac {q : alpha → ℝ} (hq : Measurable q)
    (t : NNReal) {f : alpha → ℝ} (hf : Measurable f) :
    Measurable (IsConservative.feynmanKac P hP q t f) := by
  have hpath : StronglyMeasurable (fun omega : ContinuousPath alpha ↦
      Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)) :=
    (((stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.neg.exp).mul
      (hf.comp (ContinuousPath.measurable_coordinateProcess (alpha := alpha) t))).stronglyMeasurable
  exact hpath.integral_kernel.measurable


/-- The Feynman--Kac operators satisfy the semigroup law. -/
theorem IsFellerKernelSemigroup.feynmanKac_add (hFeller : P.IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) {q : alpha → ℝ} (hq : Measurable q)
    {C : ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    (s t : NNReal) {f : alpha → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ y, ‖f y‖ ≤ D) (x : alpha) :
    IsConservative.feynmanKac P hP q (s + t) f x =
      IsConservative.feynmanKac P hP q s
        (IsConservative.feynmanKac P hP q t f) x := by
  let W : ContinuousPath alpha → ℝ := fun omega ↦
    Real.exp (-feynmanKacAdditiveFunctional q s omega)
  let F : ContinuousPath alpha → ℝ := fun eta ↦
    Real.exp (-feynmanKacAdditiveFunctional q t eta) * f (eta t)
  let mu : Measure (ContinuousPath alpha) := IsConservative.continuousProcess P hP x
  have hW : StronglyMeasurable[ContinuousPath.canonicalFiltration (alpha := alpha) s] W := by
    have hA : Measurable[ContinuousPath.canonicalFiltration (alpha := alpha) s]
        (fun omega ↦ -feynmanKacAdditiveFunctional q s omega) :=
      (stronglyMeasurable_feynmanKacAdditiveFunctional_canonicalFiltration hq s).measurable.neg
    exact hA.exp.stronglyMeasurable
  have hF : StronglyMeasurable F := by
    have hweight : StronglyMeasurable fun eta : ContinuousPath alpha ↦
        Real.exp (-feynmanKacAdditiveFunctional q t eta) :=
      (stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.neg.exp.stronglyMeasurable
    exact hweight.mul ((hf.comp
      (ContinuousPath.measurable_coordinateProcess (alpha := alpha) t)).stronglyMeasurable)
  have hFbound : ∀ eta : ContinuousPath alpha, ‖F eta‖ ≤ D := by
    intro eta
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-feynmanKacAdditiveFunctional q t eta) * ‖f (eta t)‖ ≤ 1 * ‖f (eta t)‖ :=
        mul_le_mul_of_nonneg_right
          ((Real.exp_le_one_iff).mpr
            (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 t eta))) (norm_nonneg _)
      _ ≤ D := by simpa only [one_mul] using hfD _
  have hWFbound : ∀ omega : ContinuousPath alpha,
      ‖W omega * F (ContinuousPath.shift s omega)‖ ≤ D := by
    intro omega
    rw [norm_mul]
    calc
      ‖W omega‖ * ‖F (ContinuousPath.shift s omega)‖ ≤ 1 * ‖F (ContinuousPath.shift s omega)‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        dsimp only [W]
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact (Real.exp_le_one_iff).mpr
          (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 s omega))
      _ ≤ D := by simpa only [one_mul] using hFbound _
  have hIntFshift : Integrable (fun omega ↦ F (ContinuousPath.shift s omega)) mu :=
    Integrable.of_bound
      (hF.comp_measurable
        (ContinuousPath.measurable_shift_fixed (alpha := alpha) s)).aestronglyMeasurable
      D (Eventually.of_forall fun omega ↦ hFbound _)
  have hIntWF : Integrable (fun omega ↦ W omega * F (ContinuousPath.shift s omega)) mu :=
    Integrable.of_bound
      ((hW.mono ((ContinuousPath.canonicalFiltration (alpha := alpha)).le s)).mul
        (hF.comp_measurable
          (ContinuousPath.measurable_shift_fixed (alpha := alpha) s))).aestronglyMeasurable
      D (Eventually.of_forall hWFbound)
  have hcond := hFeller.continuousProcess_condExp_shift P hP hK x s F hF D hFbound
  have hpull := condExp_mul_of_stronglyMeasurable_left (μ := mu) hW hIntWF hIntFshift
  have htotal : (fun omega ↦
      Real.exp (-feynmanKacAdditiveFunctional q (s + t) omega) * f (omega (s + t))) =
      fun omega ↦ W omega * F (ContinuousPath.shift s omega) := by
    funext omega
    dsimp only [W, F]
    rw [ContinuousPath.shift_apply, feynmanKacAdditiveFunctional_add hq hq0 hqC]
    rw [neg_add, Real.exp_add]
    ring
  rw [IsConservative.feynmanKac_apply, htotal]
  calc
    (∫ omega, W omega * F (ContinuousPath.shift s omega) ∂mu) =
        ∫ omega, mu[fun eta ↦ W eta * F (ContinuousPath.shift s eta)|
          ContinuousPath.canonicalFiltration (alpha := alpha) s] omega ∂mu := by
            rw [integral_condExp ((ContinuousPath.canonicalFiltration (alpha := alpha)).le s)]
    _ = ∫ omega, W omega *
          (∫ eta, F eta ∂IsConservative.continuousProcess P hP (omega s)) ∂mu := by
            refine integral_congr_ae (hpull.trans ?_)
            exact EventuallyEq.mul (EventuallyEq.refl _ _) hcond
    _ = IsConservative.feynmanKac P hP q s
          (IsConservative.feynmanKac P hP q t f) x := by
            rfl

end
end MarkovProcess.SubMarkovKernelSemigroup
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_condExp_shift
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.feynmanKac_add


