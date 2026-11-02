-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_OneSubExpAdditiveFunctionalCleanV1
-- name    : MarkovProcess_V3HRepair_OneSubExpAdditiveFunctionalCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T10:20:01.391785+00:00
-- url     : https://prove2.me/theorems/75e36883-6a90-4717-9993-52a7cd21b63e
-- title:
--   Verified MarkovProcess source repair: OneSubExpAdditiveFunctionalCleanV1
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess OneSubExpAdditiveFunctionalCleanV1 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.OneSubExpAdditiveFunctionalCleanV1 source SHA-256 7e7efad7b0a7a289b2c644acdb75e6e4144e5bb6b782e8d514e9f27cf3fcc6c4. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacFunctional_cc8a1986
import Definitions.Def_MarkovProcess_V3HRepair_FeynmanKacFunctionalCoreCleanV1
import Definitions.Def_MarkovProcess_V3HRepair_ExpPrimitiveCleanV1

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
variable [SecondCountableTopology alpha]

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
/-- Pathwise exponential-integral identity for the accumulated potential. -/
theorem one_sub_exp_neg_feynmanKacAdditiveFunctional {q : alpha → ℝ}
    (hq : Measurable q) {C : ℝ} (hq0 : ∀ y, 0 ≤ q y)
    (hqC : ∀ y, q y ≤ C) (t : NNReal) (omega : ContinuousPath alpha) :
    1 - Real.exp (-feynmanKacAdditiveFunctional q t omega) =
      ∫ s in (0 : ℝ)..t, q (omega (Real.toNNReal s)) *
        Real.exp (-(feynmanKacAdditiveFunctional q t omega -
          feynmanKacAdditiveFunctional q (Real.toNNReal s) omega)) := by
  let a : ℝ → ℝ := fun s ↦ q (omega (Real.toNNReal s))
  have ha : IntegrableOn a (Icc (0 : ℝ) (t : ℝ)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mp
      (intervalIntegrable_potential_path hq hq0 hqC omega 0 t)
  have hprimitive := intervalIntegral.integral_mul_exp_primitive
    (right_mem_Icc.mpr t.coe_nonneg) ha
    (fun s _ ↦ hq0 _) (fun s _ ↦ hqC _)
  have hscaled := congrArg (fun z : ℝ ↦ Real.exp
      (-feynmanKacAdditiveFunctional q t omega) * z) hprimitive
  change Real.exp (-feynmanKacAdditiveFunctional q t omega) *
      (∫ s in (0 : ℝ)..t, a s * Real.exp (∫ r in (0 : ℝ)..s, a r)) =
    Real.exp (-feynmanKacAdditiveFunctional q t omega) *
      (Real.exp (∫ r in (0 : ℝ)..t, a r) - 1) at hscaled
  rw [← intervalIntegral.integral_const_mul] at hscaled
  simp only [a, ← feynmanKacAdditiveFunctional_apply] at hscaled
  calc
    1 - Real.exp (-feynmanKacAdditiveFunctional q t omega) =
        Real.exp (-feynmanKacAdditiveFunctional q t omega) *
          (Real.exp (feynmanKacAdditiveFunctional q t omega) - 1) := by
            rw [mul_sub, ← Real.exp_add]
            simp only [neg_add_cancel, Real.exp_zero, mul_one]
    _ = ∫ s in (0 : ℝ)..t, Real.exp (-feynmanKacAdditiveFunctional q t omega) *
          (q (omega (Real.toNNReal s)) *
            Real.exp (∫ r in (0 : ℝ)..s, q (omega (Real.toNNReal r)))) := hscaled.symm
    _ = ∫ s in (0 : ℝ)..t, q (omega (Real.toNNReal s)) *
          Real.exp (-(feynmanKacAdditiveFunctional q t omega -
            feynmanKacAdditiveFunctional q (Real.toNNReal s) omega)) := by
            refine intervalIntegral.integral_congr fun s hs ↦ ?_
            have hs0 : 0 ≤ s := by
              rw [uIcc_of_le t.coe_nonneg] at hs
              exact hs.1
            have hAs : feynmanKacAdditiveFunctional q (Real.toNNReal s) omega =
                ∫ r in (0 : ℝ)..s, q (omega (Real.toNNReal r)) := by
              rw [feynmanKacAdditiveFunctional_apply, Real.coe_toNNReal s hs0]
            rw [hAs]
            rw [neg_sub, Real.exp_sub, Real.exp_neg]
            field_simp [Real.exp_ne_zero]


end
end MarkovProcess.SubMarkovKernelSemigroup
#print axioms MarkovProcess.SubMarkovKernelSemigroup.one_sub_exp_neg_feynmanKacAdditiveFunctional


