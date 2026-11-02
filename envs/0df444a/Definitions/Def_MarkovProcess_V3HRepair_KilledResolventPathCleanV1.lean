-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_KilledResolventPathCleanV1
-- name    : MarkovProcess_V3HRepair_KilledResolventPathCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T09:45:58.868456+00:00
-- url     : https://prove2.me/theorems/baedf44c-6578-4117-a4f3-54a93d9e4b22
-- title:
--   Verified MarkovProcess source repair: KilledResolventPathCleanV1
-- statement:
--   Integral representations of killed kernels and killed resolvents along continuous-path trajectories.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream commit 1f8060caa137731fa08029592019eeaf9d997fe5; source-faithful adapted axiom-clean proof module V3HRepaired.KilledResolventPathCleanV1, archived SHA-256 26dca2cb36e70e74ef35a3884a6184d7517ff109f3665725d9e9a24cb1731411.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Killed_Resolvent_b61459c1

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace MarkovProcess.SubMarkovKernelSemigroup
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)

/-- An integral against a killed kernel is an integral over the survival event. -/
theorem IsConservative.lintegral_killedKernel (t : NNReal) (x : alpha) {f : alpha → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ y, f y ∂(IsConservative.killedKernel P hP U hU t x) =
      ∫⁻ omega, {omega : ContinuousPath alpha | (t : ℝ≥0∞) < ContinuousPath.exitTime U omega}.indicator
        (fun omega ↦ f (omega t)) omega ∂(IsConservative.continuousProcess P hP x) := by
  have hmeas : Measurable (fun omega : ContinuousPath alpha ↦ omega t) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) t
  rw [IsConservative.killedKernel_eq_map, lintegral_map hf hmeas,
    ← lintegral_indicator (ContinuousPath.measurableSet_lt_exitTime U hU t)]

/-- **The killed resolvent on path space.**  For nonnegative extended measurable `f` and `lam > 0`
(only the measurability is used),
`killedResolvent lam f x = E_x ∫_0^{τ_U} e^{-lam t} f(ω_t) dt`, the time integral being cut off at
the exit time by the survival indicator. -/
theorem IsConservative.killedResolvent_eq_lintegral (lam : ℝ) {f : alpha → ℝ≥0∞}
    (hf : Measurable f) (x : alpha) :
    IsConservative.killedResolvent P hP U hU lam f x =
      ∫⁻ omega, (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
          {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega}.indicator
            (fun t ↦ f (omega (Real.toNNReal t))) t)
        ∂(IsConservative.continuousProcess P hP x) := by
  have heval : Measurable fun p : ℝ × ContinuousPath alpha ↦ p.2 (Real.toNNReal p.1) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hS : MeasurableSet {p : ℝ × ContinuousPath alpha |
      ((Real.toNNReal p.1 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U p.2} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp (measurable_real_toNNReal.comp measurable_fst))
      ((ContinuousPath.measurable_exitTime U hU).comp measurable_snd)
  have hjoint : Measurable (Function.uncurry fun (t : ℝ) (omega : ContinuousPath alpha) ↦
      ENNReal.ofReal (Real.exp (-lam * t)) *
        {omega : ContinuousPath alpha |
          ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega}.indicator
          (fun omega ↦ f (omega (Real.toNNReal t))) omega) := by
    have hrw : (Function.uncurry fun (t : ℝ) (omega : ContinuousPath alpha) ↦
        ENNReal.ofReal (Real.exp (-lam * t)) *
          {omega : ContinuousPath alpha |
            ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega}.indicator
            (fun omega ↦ f (omega (Real.toNNReal t))) omega) =
        fun p : ℝ × ContinuousPath alpha ↦ ENNReal.ofReal (Real.exp (-lam * p.1)) *
          {p : ℝ × ContinuousPath alpha |
            ((Real.toNNReal p.1 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U p.2}.indicator
            (fun p ↦ f (p.2 (Real.toNNReal p.1))) p := by
      funext p
      simp only [Function.uncurry, Set.indicator_apply, Set.mem_ofPred_eq]
    rw [hrw]
    refine Measurable.mul ?_ ((hf.comp heval).indicator hS)
    exact ENNReal.measurable_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
        measurable_fst)
  have hinner : ∀ t : ℝ, ENNReal.ofReal (Real.exp (-lam * t)) *
      ∫⁻ y, f y ∂(IsConservative.killedKernel P hP U hU (Real.toNNReal t) x) =
      ∫⁻ omega, ENNReal.ofReal (Real.exp (-lam * t)) *
        {omega : ContinuousPath alpha |
          ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega}.indicator
          (fun omega ↦ f (omega (Real.toNNReal t))) omega ∂(IsConservative.continuousProcess P hP x) := by
    intro t
    have hg : Measurable (fun omega : ContinuousPath alpha ↦ f (omega (Real.toNNReal t))) :=
      hf.comp (ContinuousPath.measurable_coordinateProcess (alpha := alpha) _)
    rw [IsConservative.lintegral_killedKernel P hP U hU _ x hf]
    exact (lintegral_const_mul _ (hg.indicator (ContinuousPath.measurableSet_lt_exitTime U hU _))).symm
  unfold IsConservative.killedResolvent
  simp_rw [hinner]
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  refine lintegral_congr fun omega ↦ ?_
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro t _
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]


end MarkovProcess.SubMarkovKernelSemigroup
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsConservative.lintegral_killedKernel
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedResolvent_eq_lintegral


