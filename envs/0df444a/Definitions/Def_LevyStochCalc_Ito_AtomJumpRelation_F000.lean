-- Prove2me | Definitions.Def_LevyStochCalc_Ito_AtomJumpRelation_F000
-- name    : LevyStochCalc_Ito_AtomJumpRelation_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:34:09.294473+00:00
-- url     : https://prove2.me/theorems/fdd33f00-8188-468a-9a54-5aea4088fb53
-- title:
--   Source declarations: LevyStochCalc.Ito.AtomJumpRelation
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.AtomJumpRelation. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSplittingPathDecomposition_F000
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingPathSums_F000
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingPathSums_F001
import Definitions.Def_LevyStochCalc_Ito_JumpSumIdentity_F000
import Definitions.Def_LevyStochCalc_Ito_JumpSumIdentity_F001
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Rat.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The left-limit jump sum as a step function of the arrival times

Over a window of finite intensity a Poisson random measure is a finite sum of Dirac masses
carried by pairwise distinct times, so the integral of a function against it over an initial
segment of the window is the plain sum of the function's values at the atoms whose time has been
reached. Read at the jump coefficient along the left limits of a path, this writes the
left-limit jump sum over the window as a step function of the arrival times.

## Main statements

* `LevyStochCalc.Poisson.setIntegral_Ioc_prod_eq_sum_filter` — the integral over an initial
  segment of the window is the sum over the atoms whose time has been reached.
* `LevyStochCalc.Poisson.stochasticIntegral_add_setIntegral_sub_eq_pathwise_sub` — the jump side
  of the Itô–Lévy formula at finite activity reads the integrand only at the atoms.
* `LevyStochCalc.Poisson.stochasticIntegral_eq_neg_setIntegral_of_atoms_zero` — an integrand
  vanishing at every atom of the window has compensated integral minus its compensator, on the
  set of sample points where the vanishing holds.
* `LevyStochCalc.Ito.JumpSplitting.tendsto_nhdsLT_sum_filter_le` — the left limit of a step
  function with finitely many steps drops the steps at the point itself.
* `LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jumpSumLeftAt_eq_sum` — the left-limit
  jump sum over the window is that step function.
* `LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jump_eq_gamma` — the increment of a path
  across an arrival time is the jump coefficient at the left limit there.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v w

section Restriction

variable {E : Type v} [MeasurableSpace E]

/-- The integral over an initial segment of a window whose integrals against a measure are finite
sums over the window's atoms is the sum over the atoms whose time has been reached. -/
theorem setIntegral_Ioc_prod_eq_sum_filter {μ : Measure (ℝ × E)} {A : Set E}
    (hA : MeasurableSet A) {T : ℝ} {K : ℕ} {θ : Fin K → ℝ} {ε : Fin K → E}
    (hmem : ∀ j, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂μ = ∑ j : Fin K, g (θ j, ε j))
    {t : ℝ} (ht : t ≤ T) (g : ℝ × E → ℝ) :
    ∫ p in Set.Ioc (0 : ℝ) t ×ˢ A, g p ∂μ
      = ∑ j ∈ Finset.univ.filter fun j => θ j ≤ t, g (θ j, ε j) := by
  classical
  have hms : MeasurableSet (Set.Ioc (0 : ℝ) t ×ˢ A) := measurableSet_Ioc.prod hA
  have hsub : Set.Ioc (0 : ℝ) t ×ˢ A ⊆ Set.Ioc (0 : ℝ) T ×ˢ A :=
    Set.prod_mono (Set.Ioc_subset_Ioc_right ht) subset_rfl
  have hind : ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A,
      Set.indicator (Set.Ioc (0 : ℝ) t ×ˢ A) g p ∂μ
      = ∫ p in Set.Ioc (0 : ℝ) t ×ˢ A, g p ∂μ := by
    rw [setIntegral_indicator hms, Set.inter_eq_self_of_subset_right hsub]
  rw [← hind, hsum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : θ j ≤ t
  · have hp : ((θ j, ε j) : ℝ × E) ∈ Set.Ioc (0 : ℝ) t ×ˢ A :=
      ⟨⟨(hmem j).1.1, hj⟩, (hmem j).2⟩
    rw [if_pos hj, Set.indicator_of_mem hp]
  · have hp : ((θ j, ε j) : ℝ × E) ∉ Set.Ioc (0 : ℝ) t ×ˢ A := fun hp => hj hp.1.2
    rw [if_neg hj, Set.indicator_of_notMem hp]
end Restriction

section JumpSide

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- **The jump side of the Itô–Lévy formula at finite activity.** The compensated integral of a
predictable integrand carried by a window of finite intensity, plus the intensity integral of
that integrand minus a correction, is the integral of the integrand against the random measure
minus the intensity integral of the correction. The integrand itself cancels, so only its values
at the atoms of the window and the correction survive. -/
theorem stochasticIntegral_add_setIntegral_sub_eq_pathwise_sub
    (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsPoissonFiltration N ℱ) (φ ψ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {A : Set E} (hA : MeasurableSet A) (hφpred : Probability.MarkedPredictable ℱ ν φ)
    (hAν : ν A ≠ ⊤) (hsupp : ∀ ω s e, e ∉ A → φ ω s e = 0) {T : ℝ} (hT : 0 < T)
    (hφint : ∀ᵐ ω ∂P, IntegrableOn (fun q : ℝ × E => φ ω q.1 q.2)
      (Set.Ioc (0 : ℝ) T ×ˢ A) (referenceIntensity ν))
    (hψint : ∀ᵐ ω ∂P, IntegrableOn (fun q : ℝ × E => ψ ω q.1 q.2)
      (Set.Ioc (0 : ℝ) T ×ˢ A) (referenceIntensity ν)) :
    ∀ᵐ ω ∂P,
      Compensated.stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq T ω
          + ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, (φ ω q.1 q.2 - ψ ω q.1 q.2) ∂(referenceIntensity ν)
        = (∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, φ ω q.1 q.2 ∂(N.N ω))
          - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, ψ ω q.1 q.2 ∂(referenceIntensity ν) := by
  filter_upwards [Compensated.stochasticIntegral_ae_eq_pathwise N ℱ hℱ φ h_meas h_progMeas h_sq
    hA hφpred hAν hsupp hT, hφint, hψint] with ω hpath hφω hψω
  rw [hpath, integral_sub hφω hψω]
  ring
/-- **A predictable integrand vanishing at the atoms of a window of finite intensity has
compensated integral minus its compensator.** -/
theorem stochasticIntegral_eq_neg_setIntegral_of_atoms_zero
    (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {A : Set E} (hA : MeasurableSet A) (hφpred : Probability.MarkedPredictable ℱ ν φ)
    (hAν : ν A ≠ ⊤) (hsupp : ∀ ω s e, e ∉ A → φ ω s e = 0) {T : ℝ} (hT : 0 < T) (G : Set Ω)
    (hatoms : ∀ᵐ ω ∂P, ω ∈ G →
      ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, φ ω q.1 q.2 ∂(N.N ω) = 0) :
    ∀ᵐ ω ∂P, ω ∈ G →
      Compensated.stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq T ω
        = -∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, φ ω q.1 q.2 ∂(referenceIntensity ν) := by
  filter_upwards [Compensated.stochasticIntegral_ae_eq_pathwise N ℱ hℱ φ h_meas h_progMeas h_sq
    hA hφpred hAν hsupp hT, hatoms] with ω hpath hzero hG
  rw [hpath, hzero hG, zero_sub]
end JumpSide

end LevyStochCalc.Poisson

namespace LevyStochCalc.Ito.JumpSplitting

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

end LevyStochCalc.Ito.JumpSplitting


