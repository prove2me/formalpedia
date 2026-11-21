-- Prove2me | Definitions.Def_LevyStochCalc_Ito_SecondMomentToolkit_F002
-- name    : LevyStochCalc_Ito_SecondMomentToolkit_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:20:41.877014+00:00
-- url     : https://prove2.me/theorems/05c885ef-97a1-49dc-825d-8075f8522fba
-- title:
--   Source declarations: LevyStochCalc.Ito.SecondMomentToolkit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.SecondMomentToolkit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F001
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.Upcrossing
import Mathlib.Probability.Notation
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Auxiliary lemmas for the second moment of an Itô–Lévy process

The `L²` lemmas behind the expectation form of the quadratic Itô formula: the second moment of a
square-integrable variable as the real part of its energy, the expansion of the square of a sum,
the evaluation of a square-integrable martingale paired against a variable measurable at an
earlier time, and the exchange of a time integral with a pairing. The running integral
`∫_0^s b_r dr` of a drift over a window `[0, T]` is introduced as a jointly measurable function of
the sample point and the time, together with the pathwise identities
`(∫_0^T b)² = 2 ∫_0^T (∫_0^s b) b_s ds` and, for two integrable functions,
`(∫_0^T b)(∫_0^T b') = ∫_0^T ((∫_0^s b) b'_s + b_s (∫_0^s b')) ds`; and the polarised isometry for
the Brownian integral, the expected product of two Brownian integrals at a time being the expected
time integral of the product of their integrands.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Toolkit

omit [IsProbabilityMeasure P] in
/-- A window energy finite at every positive horizon is finite at every nonnegative one. -/
theorem energy_lt_top_of_nonneg {f : Ω → ℝ → ℝ}
    (hfq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  lt_of_le_of_lt (lintegral_mono fun _ => lintegral_mono_set
    (Set.Icc_subset_Icc le_rfl (by linarith))) (hfq (t + 1) (by linarith))
/-- At almost every time of a window, a square-integrable integrand is square integrable in the
sample point. -/
theorem ae_memLp_two_eval {f : Ω → ℝ → ℝ} (hf : Measurable (Function.uncurry f)) {T : ℝ}
    (hfq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (fun ω => f ω s) 2 P := by
  have hm : Measurable fun p : Ω × ℝ => (‖f p.1 p.2‖₊ : ℝ≥0∞) ^ 2 :=
    hf.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hswap : ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂P ∂volume < ⊤ := by
    rw [lintegral_lintegral_swap (f := fun ω s => (‖f ω s‖₊ : ℝ≥0∞) ^ 2) hm.aemeasurable] at hfq
    exact hfq
  have hmeas : Measurable fun s => ∫⁻ ω, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂P :=
    Measurable.lintegral_prod_left' hm
  filter_upwards [ae_lt_top hmeas hswap.ne] with s hs
  exact LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top
    (hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable hs
end Toolkit

section Running

variable (b : ℝ → Ω → ℝ) (T : ℝ)

/-- The running integral `∫_0^s b_r dr`, written as an integral over the fixed window `[0, T]`
so that it is jointly measurable in the sample point and the time. -/
noncomputable def running (p : Ω × ℝ) : ℝ :=
  ∫ r in Set.Icc (0 : ℝ) T, (Set.Iic p.2).indicator (fun r => b r p.1) r
variable {b T}

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem running_eq {ω : Ω} {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    running b T (ω, s) = ∫ r in Set.Icc (0 : ℝ) s, b r ω := by
  have hset : Set.Iic s ∩ Set.Icc (0 : ℝ) T = Set.Icc (0 : ℝ) s := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨h1, h2, h1.trans hs.2⟩
  rw [running, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    hset]
omit [IsProbabilityMeasure P] in
theorem stronglyMeasurable_running (hbm : Measurable (Function.uncurry fun ω s => b s ω)) :
    StronglyMeasurable (running b T) := by
  have hfun : (fun q : (Ω × ℝ) × ℝ => (Set.Iic q.1.2).indicator (fun r => b r q.1.1) q.2)
      = {q : (Ω × ℝ) × ℝ | q.2 ≤ q.1.2}.indicator fun q => b q.2 q.1.1 := by
    funext q
    by_cases hq : q.2 ≤ q.1.2 <;> simp [Set.indicator, hq]
  have hm : Measurable fun q : (Ω × ℝ) × ℝ =>
      (Set.Iic q.1.2).indicator (fun r => b r q.1.1) q.2 := by
    rw [hfun]
    exact (hbm.comp (measurable_fst.fst.prodMk measurable_snd)).indicator
      (measurableSet_le measurable_snd measurable_fst.snd)
  exact hm.stronglyMeasurable.integral_prod_right'
end Running

section Polarised

end Polarised

section PolarisedDrift

end PolarisedDrift

end LevyStochCalc.Ito.SecondMoment


