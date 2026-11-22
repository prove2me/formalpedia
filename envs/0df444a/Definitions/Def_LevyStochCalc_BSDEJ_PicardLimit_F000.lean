-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_PicardLimit_F000
-- name    : LevyStochCalc_BSDEJ_PicardLimit_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:10:39.642274+00:00
-- url     : https://prove2.me/theorems/d01c6e19-110c-4940-83f3-788b9285c050
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.PicardLimit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.PicardLimit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_DriftModification_F001
import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionBounds_F000
import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionContraction_F000
import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionNorm_F000
import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionNorm_F001
import Definitions.Def_LevyStochCalc_BSDEJ_PicardIteratesCauchy_F000
import Definitions.Def_LevyStochCalc_BSDEJ_PicardIteratesCauchy_F001
import Definitions.Def_LevyStochCalc_BSDEJ_PicardIteratesStep_F000
import Definitions.Def_LevyStochCalc_Driver_Joint_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIntegrandComplete_F001
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.SetToL1
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.Upcrossing
import Mathlib.Probability.Notation
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The limit of the Picard iterates and existence of a solution

The Picard iterates of a backward equation with jumps are Cauchy for the energy of the value
process, for the energies of the diffusion coordinates and for the marked energy of the jump
integrand, so completeness of the admissible integrands produces an admissible limit triple
which the iterates approach in the exponentially weighted norm at the Young weight
`max 2 (24 L²)`. A further Picard step along the limit triple contracts that distance by `1/4`
against every iterate, so its output is at zero weighted distance from the limit triple; a
Lipschitz generator takes the same value along two triples agreeing almost everywhere on
`Ω × [0, T]`, so the output is its own Picard output and solves the equation.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.PicardOutput.congr_inputs` — a Picard output along one input
  triple is a Picard output along any input triple agreeing with it almost everywhere on the
  horizon.
* `LevyStochCalc.BSDEJ.Solves.exists_admissible_wNorm_limit` — an energy-Cauchy sequence of
  admissible triples converges in the weighted norm to an admissible triple.
* `LevyStochCalc.BSDEJ.Solves.exists_solvesBSDEJ` — a backward equation with jumps whose
  generator is Lipschitz and square integrable at the origin and whose terminal datum is square
  integrable has a solution.

## References

* Tang–Li, *Necessary conditions for optimal control of stochastic systems with random jumps*,
  SIAM J. Control Optim. 32 (1994), §2.
* Barles–Buckdahn–Pardoux, *BSDEs and integral-partial differential equations*, Stochastics 60
  (1997), §2.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Truncation to the horizon -/

/-- Restricting the times of a progressively measurable process to a measurable set preserves
progressive measurability. -/
theorem progressivelyMeasurable_indicator_time {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {H : Ω → ℝ → ℝ} (h : Probability.ProgressivelyMeasurable ℱ H) {S : Set ℝ}
    (hS : MeasurableSet S) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => S.indicator (fun _ => H ω s) s := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hrw : (fun p : Ω × ℝ =>
        (Set.Iic t).indicator (fun s => S.indicator (fun _ => H p.1 s) s) p.2)
      = {p : Ω × ℝ | p.2 ∈ S}.indicator fun p => (Set.Iic t).indicator (H p.1) p.2 := by
    funext p
    by_cases ht : p.2 ∈ Set.Iic t <;> by_cases hp : p.2 ∈ S <;> simp [ht, hp]
  rw [hrw]
  exact (h t).indicator (measurable_snd hS)
omit [IsProbabilityMeasure P] in
/-- Processes agreeing on the horizon have the same energy there. -/
theorem energy_congr_on_Icc {T : ℝ} {H K : Ω → ℝ → ℝ}
    (h : ∀ ω : Ω, ∀ s ∈ Set.Icc (0 : ℝ) T, H ω s = K ω s) :
    Brownian.Ito.energy P T H = Brownian.Ito.energy P T K :=
  lintegral_congr fun ω =>
    setLIntegral_congr_fun measurableSet_Icc fun s hs => by rw [h ω s hs]
/-! ### Changing the input triple of a Picard step on a null set -/

/-! ### Triples at zero weighted distance -/

/-! ### The weighted norm against the energies -/

/-! ### The limit of an energy-Cauchy sequence of admissible triples -/

section Limit

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {T : ℝ}

end Limit

/-! ### The fixed point of the Picard step -/

section FixedPoint

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L T : ℝ} {ξ : Ω → ℝ}

end FixedPoint

/-! ### Existence of a solution -/

end LevyStochCalc.BSDEJ.Solves


