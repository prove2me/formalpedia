-- Prove2me | Definitions.Def_LevyStochCalc_Ito_SecondMomentWeighted_F000
-- name    : LevyStochCalc_Ito_SecondMomentWeighted_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:25:04.027461+00:00
-- url     : https://prove2.me/theorems/9c6f3683-1336-47ff-a2be-a97e283a4b06
-- title:
--   Source declarations: LevyStochCalc.Ito.SecondMomentWeighted
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.SecondMomentWeighted. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_Joint_F000
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
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.Upcrossing
import Mathlib.Probability.Notation
import Mathlib.Probability.Process.Adapted
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
# The exponentially weighted second moment of an Itô–Lévy process

The map `t ↦ 𝔼[X_t²]` is the initial value plus the time integral of the rate
`2 𝔼[X_s b_s] + ∑_j 𝔼[σ_j(s)²] + 𝔼 ∫_E γ(s, e)² ν(de)`, so integration by parts against the
weight `e^{βs}` gives

`e^{βT} 𝔼[X_T²] = 𝔼[X₀²] + ∫_0^T e^{βs} (β 𝔼[X_s²] + 2 𝔼[X_s b_s] + ∑_j 𝔼[σ_j(s)²]
  + 𝔼 ∫_E γ(s, e)² ν(de)) ds`,

the form in which the a-priori estimates for BSDEs with jumps read the quadratic formula. The
weighting of an absolutely continuous function by an exponential is isolated first, as a real
identity. The vector form follows coordinatewise, and the cross witness carried by the driver
gives the bilinear and the weighted forms over its augmented joint natural filtration.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Weight

/-! ### The exponential weight: integration by parts against `e^{βs}` -/

/-- A finite window energy is the time integral of the sample energies at each time. -/
theorem toReal_lintegral_lintegral_eq {F : Ω → ℝ → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) {T : ℝ}
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, F ω s ∂volume ∂P < ⊤) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, F ω s ∂volume ∂P).toReal
      = ∫ s in Set.Icc (0 : ℝ) T, (∫⁻ ω, F ω s ∂P).toReal := by
  have hswap : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, F ω s ∂volume ∂P
      = ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω, F ω s ∂P ∂volume :=
    lintegral_lintegral_swap (μ := P) (ν := volume.restrict (Set.Icc (0 : ℝ) T)) hF.aemeasurable
  have hm : Measurable fun s => ∫⁻ ω, F ω s ∂P := hF.lintegral_prod_left
  rw [hswap, integral_toReal hm.aemeasurable]
  exact ae_lt_top hm (by rw [← hswap]; exact hfin.ne)
/-- The sample energies of a finite window energy are integrable in time. -/
theorem integrableOn_toReal_lintegral {F : Ω → ℝ → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) {T : ℝ}
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, F ω s ∂volume ∂P < ⊤) :
    IntegrableOn (fun s => (∫⁻ ω, F ω s ∂P).toReal) (Set.Icc (0 : ℝ) T) := by
  have hswap : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, F ω s ∂volume ∂P
      = ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω, F ω s ∂P ∂volume :=
    lintegral_lintegral_swap (μ := P) (ν := volume.restrict (Set.Icc (0 : ℝ) T)) hF.aemeasurable
  exact integrable_toReal_of_lintegral_ne_top hF.lintegral_prod_left.aemeasurable
    (by rw [← hswap]; exact hfin.ne)
/-- The integral of `β e^{βs}` over `[r, T]`. -/
theorem setIntegral_mul_exp_mul (β : ℝ) {r T : ℝ} (hrT : r ≤ T) :
    ∫ s in Set.Icc r T, β * Real.exp (β * s) = Real.exp (β * T) - Real.exp (β * r) := by
  have hder : ∀ x : ℝ, HasDerivAt (fun s => Real.exp (β * s)) (β * Real.exp (β * x)) x := by
    intro x
    have := ((hasDerivAt_id' (x := x)).const_mul β).exp
    convert this using 1
    ring
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hrT]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x)
    ((by fun_prop : Continuous fun s : ℝ => β * Real.exp (β * s)).intervalIntegrable _ _)
end Weight

section Weighted

/-! ### The exponentially weighted second moment -/

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

end Weighted

section WeightedVector

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d n : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : Fin n → ℝ → Ω → ℝ} {X₀ : Fin n → Ω → ℝ} {b : Fin n → ℝ → Ω → ℝ}
  {σ : Fin n → ℝ → Ω → Fin d → ℝ} {γ : Fin n → Ω → ℝ → E → ℝ}

end WeightedVector

section AugmentedMore

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

end AugmentedMore

end LevyStochCalc.Ito.SecondMoment


