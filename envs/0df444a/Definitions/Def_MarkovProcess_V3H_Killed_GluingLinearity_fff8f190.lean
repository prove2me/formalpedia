-- Prove2me | Definitions.Def_MarkovProcess_V3H_Killed_GluingLinearity_fff8f190
-- name    : MarkovProcess_V3H_Killed_GluingLinearity_fff8f190
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:25:54.374613+00:00
-- url     : https://prove2.me/theorems/bd60bfc5-39c6-4d6a-a52a-497fe33a899c
-- title:
--   MarkovProcess: MarkovProcess_V3H_Killed_GluingLinearity_fff8f190
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0Resolvent_c009f25c
import Definitions.Def_MarkovProcess_V3H_Kernel_Resolvent_f63a7282
import Definitions.Def_MarkovProcess_V3H_Killed_GluingMinimal_1c9dd1e4
import Definitions.Def_MarkovProcess_V3H_Killed_GluingPotential_fe882cb0
import Definitions.Def_MarkovProcess_V3H_Killed_GluingResolventEquation_b19dddc8
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
# Linearity of the transported local resolvents and of their supremum

The transported local resolvents of `Killed/GluingMinimal.lean` inherit additivity and
homogeneity from the kernel resolvents they extend (`localResolvent_add`,
`localResolvent_const_mul`).  Homogeneity passes to the supremum without further hypotheses
(`minimalResolvent_const_mul`), while additivity passes to it exactly when the transported
resolvents are monotone in the index, so that the two suprema can be added term by term
(`minimalResolvent_add`).

A uniformly bounded observable has a uniformly bounded supremum resolvent: at the shift `lam`
the bound is the bound of the observable divided by `lam`
(`minimalResolvent_le_of_le_const`), so the value is finite (`minimalResolvent_ne_top`).  This
is the estimate which makes the real-valued form of the supremum resolvent well defined.

The transported resolvents at two shifts commute (`localResolvent_comm`), and so do their
suprema once the family is monotone in the index (`minimalResolvent_comm`).

Nothing here uses the part-process identity; monotonicity in the index is a bare hypothesis.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess

variable {alpha : Type*} [MeasurableSpace alpha] {X : ℕ → Type*}
  [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)] [∀ m, BorelSpace (X m)]

variable (R : ∀ m, PositiveC0ContractiveResolvent (X m)) (emb : ∀ m, X m → alpha)

/-- The transported resolvent is additive on measurable observables. -/
theorem localResolvent_add {m : ℕ} (hemb : MeasurableEmbedding (emb m)) (lam : ℝ)
    {f g : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    localResolvent R emb m lam (fun y ↦ f y + g y) x =
      localResolvent R emb m lam f x + localResolvent R emb m lam g x := by
  by_cases hx : x ∈ Set.range (emb m)
  · obtain ⟨y, rfl⟩ := hx
    rw [localResolvent_apply R emb hemb.injective lam _ y,
      localResolvent_apply R emb hemb.injective lam f y,
      localResolvent_apply R emb hemb.injective lam g y]
    exact (R m).kernelSemigroup.kernelResolvent_add lam (hf.comp hemb.measurable) y
  · rw [localResolvent_of_notMem R emb m lam _ hx, localResolvent_of_notMem R emb m lam f hx,
      localResolvent_of_notMem R emb m lam g hx, add_zero]

/-- The transported resolvent is homogeneous under multiplication by an extended-real
constant. -/
theorem localResolvent_const_mul {m : ℕ} (hemb : MeasurableEmbedding (emb m)) (lam : ℝ)
    (c : ℝ≥0∞) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    localResolvent R emb m lam (fun y ↦ c * f y) x = c * localResolvent R emb m lam f x := by
  by_cases hx : x ∈ Set.range (emb m)
  · obtain ⟨y, rfl⟩ := hx
    rw [localResolvent_apply R emb hemb.injective lam _ y,
      localResolvent_apply R emb hemb.injective lam f y]
    exact (R m).kernelSemigroup.kernelResolvent_const_mul lam c (hf.comp hemb.measurable) y
  · rw [localResolvent_of_notMem R emb m lam _ hx, localResolvent_of_notMem R emb m lam f hx,
      mul_zero]

/-- **The supremum resolvent is additive** on measurable observables, as soon as the transported
resolvents are monotone in the index: the suprema of two monotone families add term by term. -/
theorem minimalResolvent_add (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam : ℝ} (hlam : 0 < lam) {f g : alpha → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (x : alpha) :
    minimalResolvent R emb lam (fun y ↦ f y + g y) x =
      minimalResolvent R emb lam f x + minimalResolvent R emb lam g x := by
  unfold minimalResolvent
  rw [ENNReal.iSup_add_iSup_of_monotone (hmono lam hlam hf x) (hmono lam hlam hg x)]
  exact iSup_congr fun m ↦ localResolvent_add R emb (hemb m) lam hf x

/-- The supremum resolvent is homogeneous under multiplication by an extended-real constant. -/
theorem minimalResolvent_const_mul (hemb : ∀ m, MeasurableEmbedding (emb m)) (lam : ℝ)
    (c : ℝ≥0∞) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    minimalResolvent R emb lam (fun y ↦ c * f y) x = c * minimalResolvent R emb lam f x := by
  unfold minimalResolvent
  rw [ENNReal.mul_iSup]
  exact iSup_congr fun m ↦ localResolvent_const_mul R emb (hemb m) lam c hf x

/-- **The uniform bound.**  At a positive shift, a uniform bound for the observable divided by
the shift is a uniform bound for the supremum resolvent. -/
theorem minimalResolvent_le_of_le_const (hemb : ∀ m, MeasurableEmbedding (emb m))
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ≥0∞} {c : ℝ≥0∞} (hfc : ∀ y, f y ≤ c)
    (x : alpha) :
    minimalResolvent R emb lam f x ≤ c * ENNReal.ofReal lam⁻¹ := by
  calc minimalResolvent R emb lam f x
      ≤ minimalResolvent R emb lam (fun _ ↦ c * 1) x :=
        minimalResolvent_mono_of_le R emb (fun m ↦ (hemb m).injective) lam
          (fun y ↦ by simpa using hfc y) x
    _ = c * minimalResolvent R emb lam (fun _ ↦ 1) x :=
        minimalResolvent_const_mul R emb hemb lam c measurable_const x
    _ ≤ c * ENNReal.ofReal lam⁻¹ :=
        mul_le_mul' le_rfl (minimalResolvent_one_le R emb (fun m ↦ (hemb m).injective) hlam x)

/-- At a positive shift the supremum resolvent of a uniformly bounded observable is finite. -/
theorem minimalResolvent_ne_top (hemb : ∀ m, MeasurableEmbedding (emb m))
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hfc : ∀ y, f y ≤ c) (x : alpha) :
    minimalResolvent R emb lam f x ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top hc ENNReal.ofReal_ne_top)
    (minimalResolvent_le_of_le_const R emb hemb hlam hfc x)

/-- The transported resolvents at two shifts commute. -/
theorem p2m_embedded_daf80c9be41abe96 {m : ℕ} (hemb : MeasurableEmbedding (emb m)) (lam mu : ℝ)
    {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    localResolvent R emb m lam (localResolvent R emb m mu f) x =
      localResolvent R emb m mu (localResolvent R emb m lam f) x := by
  by_cases hx : x ∈ Set.range (emb m)
  · obtain ⟨y, rfl⟩ := hx
    have hinner : ∀ nu : ℝ, (fun z ↦ localResolvent R emb m nu f (emb m z)) =
        (R m).kernelSemigroup.kernelResolvent nu fun z ↦ f (emb m z) := by
      intro nu
      funext z
      exact localResolvent_apply R emb hemb.injective nu f z
    rw [localResolvent_apply R emb hemb.injective lam _ y,
      localResolvent_apply R emb hemb.injective mu _ y, hinner, hinner]
    exact (R m).kernelSemigroup.p2m_embedded_c74c9d1b92b41646 lam mu (hf.comp hemb.measurable) y
  · rw [localResolvent_of_notMem R emb m lam _ hx, localResolvent_of_notMem R emb m mu _ hx]

/-- **The supremum resolvents at two shifts commute**, as soon as the transported resolvents are
monotone in the index: each composition is the supremum of the commuting compositions along the
diagonal. -/
theorem minimalResolvent_comm (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu) {f : alpha → ℝ≥0∞} (hf : Measurable f)
    (x : alpha) :
    minimalResolvent R emb lam (minimalResolvent R emb mu f) x =
      minimalResolvent R emb mu (minimalResolvent R emb lam f) x := by
  rw [_root_.MarkovProcess.p2m_embedded_837741bc8cbb97d8 R emb hemb hmono hlam hmu hf x,
    _root_.MarkovProcess.p2m_embedded_837741bc8cbb97d8 R emb hemb hmono hmu hlam hf x]
  exact iSup_congr fun n ↦ _root_.MarkovProcess.p2m_embedded_daf80c9be41abe96 R emb (hemb n) lam mu hf x

/-- At a positive shift the supremum resolvent of the zero observable vanishes. -/
theorem minimalResolvent_zero (hemb : ∀ m, MeasurableEmbedding (emb m)) {lam : ℝ}
    (hlam : 0 < lam) (x : alpha) :
    minimalResolvent R emb lam (fun _ ↦ 0) x = 0 := by
  refine le_antisymm ?_ zero_le
  simpa using minimalResolvent_le_of_le_const R emb hemb hlam
    (f := fun _ : alpha ↦ (0 : ℝ≥0∞)) (c := 0) (fun _ ↦ le_rfl) x

end MarkovProcess


