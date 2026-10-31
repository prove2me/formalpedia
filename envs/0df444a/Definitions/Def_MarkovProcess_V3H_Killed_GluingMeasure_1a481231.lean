-- Prove2me | Definitions.Def_MarkovProcess_V3H_Killed_GluingMeasure_1a481231
-- name    : MarkovProcess_V3H_Killed_GluingMeasure_1a481231
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:27:11.425122+00:00
-- url     : https://prove2.me/theorems/6666e8d8-a83c-48a5-9730-4af02433467f
-- title:
--   MarkovProcess: MarkovProcess_V3H_Killed_GluingMeasure_1a481231
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0Resolvent_c009f25c
import Definitions.Def_MarkovProcess_V3H_Killed_GluingLinearity_fff8f190
import Definitions.Def_MarkovProcess_V3H_Killed_GluingMinimal_1c9dd1e4
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The potential measure of the supremum resolvent

Additivity and continuity along monotone limits make the supremum resolvent countably additive
on measurable observables (`minimalResolvent_tsum`), so at a positive shift it is the integral
against a finite measure on the state space, the potential measure `minimalPotential`
(`lintegral_minimalPotential`, `isFiniteMeasure_minimalPotential`).

This is the form in which the supremum resolvent is compared with the kernel resolvent of a
transition semigroup: an identity tested on continuous observables vanishing at infinity extends
to all nonnegative measurable observables through the two potential measures.

Monotonicity of the transported resolvents in the index is a bare hypothesis throughout.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace MarkovProcess

variable {alpha : Type*} [MeasurableSpace alpha] {X : ℕ → Type*}
  [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)] [∀ m, BorelSpace (X m)]

variable (R : ∀ m, PositiveC0ContractiveResolvent (X m)) (emb : ∀ m, X m → alpha)

/-- **The supremum resolvent is countably additive** on measurable observables: finite additivity
and continuity along monotone limits give the sum of a series. -/
theorem minimalResolvent_tsum (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam : ℝ} (hlam : 0 < lam) {u : ℕ → alpha → ℝ≥0∞} (hu : ∀ i, Measurable (u i))
    (x : alpha) :
    minimalResolvent R emb lam (fun y ↦ ∑' i, u i y) x =
      ∑' i, minimalResolvent R emb lam (u i) x := by
  have hpartial : ∀ N, Measurable fun y ↦ ∑ i ∈ Finset.range N, u i y := fun N ↦
    Finset.measurable_sum _ fun i _ ↦ hu i
  have hpartialMono : Monotone fun N ↦ fun y ↦ ∑ i ∈ Finset.range N, u i y := by
    intro a b hab y
    have hsub : Finset.range a ⊆ Finset.range b := Finset.range_subset_range.2 hab
    exact Finset.sum_le_sum_of_subset hsub
  have hfinite : ∀ N, minimalResolvent R emb lam (fun y ↦ ∑ i ∈ Finset.range N, u i y) x =
      ∑ i ∈ Finset.range N, minimalResolvent R emb lam (u i) x := by
    intro N
    induction N with
    | zero => simpa using minimalResolvent_zero R emb hemb hlam x
    | succ N ih =>
        have hsplit : (fun y ↦ ∑ i ∈ Finset.range (N + 1), u i y) =
            fun y ↦ (∑ i ∈ Finset.range N, u i y) + u N y := by
          funext y
          rw [Finset.sum_range_succ]
        rw [hsplit, minimalResolvent_add R emb hemb hmono hlam (hpartial N) (hu N) x, ih,
          Finset.sum_range_succ]
  have hseries : (fun y ↦ ∑' i, u i y) = fun y ↦ ⨆ N, ∑ i ∈ Finset.range N, u i y := by
    funext y
    exact ENNReal.tsum_eq_iSup_nat
  rw [hseries, minimalResolvent_iSup R emb hemb lam hpartial hpartialMono x,
    ENNReal.tsum_eq_iSup_nat]
  exact iSup_congr hfinite

omit [MeasurableSpace alpha] in
/-- The indicator of a countable disjoint union is the sum of the indicators. -/
 theorem tsum_indicator_one {S : ℕ → Set alpha}
    (hdisj : Pairwise (Function.onFun Disjoint S)) (y : alpha) :
    (⋃ i, S i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y =
      ∑' i, (S i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y := by
  by_cases hy : y ∈ ⋃ i, S i
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    have hzero : ∀ i, i ≠ j → (S i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y = 0 := by
      intro i hij
      exact Set.indicator_of_notMem
        (fun hmem ↦ Set.disjoint_left.mp (hdisj hij) hmem hj) _
    rw [Set.indicator_of_mem hy, tsum_eq_single j hzero, Set.indicator_of_mem hj]
  · have hzero : ∀ i, (S i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y = 0 := fun i ↦
      Set.indicator_of_notMem (fun hmem ↦ hy (Set.mem_iUnion.mpr ⟨i, hmem⟩)) _
    rw [Set.indicator_of_notMem hy]
    simp only [hzero, tsum_zero]

/-- **The potential measure of the supremum resolvent** at a positive shift: the measure whose
value on a measurable set is the supremum resolvent of its indicator. -/
def minimalPotential (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam : ℝ} (hlam : 0 < lam) (x : alpha) : Measure alpha :=
  Measure.ofMeasurable
    (fun S _ ↦ minimalResolvent R emb lam (S.indicator fun _ ↦ 1) x)
    (by simpa using minimalResolvent_zero R emb hemb hlam x)
    (fun {S} hS hdisj ↦ by
      have hindicator : (⋃ i, S i).indicator (fun _ ↦ (1 : ℝ≥0∞)) =
          fun y ↦ ∑' i, (S i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y := by
        funext y
        exact tsum_indicator_one hdisj y
      rw [hindicator,
        minimalResolvent_tsum R emb hemb hmono hlam
          (fun i ↦ measurable_const.indicator (hS i)) x])







end MarkovProcess


