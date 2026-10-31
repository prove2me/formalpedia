-- Prove2me | Definitions.Def_MarkovProcess_V3H_Killed_GluingMinimal_1c9dd1e4
-- name    : MarkovProcess_V3H_Killed_GluingMinimal_1c9dd1e4
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:24:50.378552+00:00
-- url     : https://prove2.me/theorems/1db96994-1b75-472a-8d43-c45bb98d8287
-- title:
--   MarkovProcess: MarkovProcess_V3H_Killed_GluingMinimal_1c9dd1e4
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0Resolvent_c009f25c
import Definitions.Def_MarkovProcess_V3H_Kernel_Resolvent_f63a7282
import Definitions.Def_MarkovProcess_V3H_Killed_GluingLocal_6bd3d344
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
# The supremum resolvent (the minimal process of Blumenthal--Getoor, in name only)

A family of positive `C₀`-contractive resolvents `R m` on local state spaces `X m`, embedded as
an increasing family of open subsets of an ambient measurable space, is glued here at the level
of resolvents.  Each `R m` is transported to the ambient space by extending its kernel resolvent
by zero off the `m`-th domain (`localResolvent`).  Under the part-process identity of
`Killed/GluingLocal.lean` -- the resolvent of the compactified process of `R (m+1)`, killed at
the exit from the image of `X m`, is `R m` -- the transported resolvents increase with `m`
(`localResolvent_le_succ`), because a path leaves the smaller domain no later and therefore
accumulates less.  Their supremum is `minimalResolvent`.

The supremum is monotone in the observable, measurable in the starting point, and sub-Markov at
every positive shift: `lam` times its value on the constant observable one is at most one
(`ofReal_mul_minimalResolvent_one_le`).  It satisfies the resolvent equation as soon as the
transported resolvents are monotone in `m`
(`minimalResolvent_resolventEquation_of_monotone`, by monotone convergence from the resolvent
equation of each member); the part-process identity enters only through that monotonicity
(`minimalResolvent_resolventEquation`).

No minimality property among resolvent families is asserted here.  The declaration names
keep the word `minimal` because the object is the resolvent of Blumenthal--Getoor's minimal
process, but that is a name and not a claim.

The regularity data of each compactification are an explicit hypothesis throughout: positivity,
contractivity and the resolvent identity do not by themselves give a compactified semigroup a
continuous-path process.

No transition semigroup, no process on the ambient space, and no conservativity are constructed
here.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess

variable {alpha : Type*} [MeasurableSpace alpha] {X : ℕ → Type*}
  [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)] [∀ m, BorelSpace (X m)]

variable (R : ∀ m, PositiveC0ContractiveResolvent (X m)) (emb : ∀ m, X m → alpha)

/-- The kernel resolvent of the `m`-th local resolvent, transported to the ambient space and
extended by zero off the `m`-th local domain. -/
noncomputable def localResolvent (m : ℕ) (lam : ℝ) (f : alpha → ℝ≥0∞) : alpha → ℝ≥0∞ :=
  Function.extend (emb m)
    (fun y ↦ (R m).kernelSemigroup.kernelResolvent lam (fun z ↦ f (emb m z)) y) 0

omit [MeasurableSpace alpha] in
/-- Inside the `m`-th local domain the transported resolvent is the `m`-th kernel resolvent. -/
theorem localResolvent_apply {m : ℕ} (hemb : Function.Injective (emb m)) (lam : ℝ)
    (f : alpha → ℝ≥0∞) (y : X m) :
    localResolvent R emb m lam f (emb m y) =
      (R m).kernelSemigroup.kernelResolvent lam (fun z ↦ f (emb m z)) y :=
  hemb.extend_apply _ _ y

omit [MeasurableSpace alpha] in
/-- Off the `m`-th local domain the transported resolvent vanishes. -/
theorem localResolvent_of_notMem (m : ℕ) (lam : ℝ) (f : alpha → ℝ≥0∞) {x : alpha}
    (hx : x ∉ Set.range (emb m)) : localResolvent R emb m lam f x = 0 :=
  Function.extend_apply' _ _ _ fun hmem ↦ hx hmem

omit [MeasurableSpace alpha] in
/-- The transported resolvent is monotone in the observable. -/
theorem localResolvent_mono_of_le {m : ℕ} (hemb : Function.Injective (emb m)) (lam : ℝ)
    {f g : alpha → ℝ≥0∞} (hfg : f ≤ g) (x : alpha) :
    localResolvent R emb m lam f x ≤ localResolvent R emb m lam g x := by
  by_cases hx : x ∈ Set.range (emb m)
  · obtain ⟨y, rfl⟩ := hx
    rw [localResolvent_apply R emb hemb lam f y, localResolvent_apply R emb hemb lam g y]
    exact (R m).kernelSemigroup.kernelResolvent_mono lam (fun z ↦ hfg (emb m z)) y
  · rw [localResolvent_of_notMem R emb m lam f hx]
    exact zero_le

/-- The transported resolvent is measurable in the starting point. -/
theorem measurable_localResolvent {m : ℕ} (hemb : MeasurableEmbedding (emb m)) (lam : ℝ)
    {f : alpha → ℝ≥0∞} (hf : Measurable f) :
    Measurable (localResolvent R emb m lam f) :=
  hemb.measurable_extend
    ((R m).kernelSemigroup.measurable_kernelResolvent lam (hf.comp hemb.measurable))
    measurable_const

/-- The transported resolvent is continuous along monotone limits of observables. -/
theorem p2m_embedded_b806785ec653a433 {m : ℕ} (hemb : MeasurableEmbedding (emb m)) (lam : ℝ)
    {f : ℕ → alpha → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) (hmono : Monotone f) (x : alpha) :
    localResolvent R emb m lam (fun y ↦ ⨆ n, f n y) x =
      ⨆ n, localResolvent R emb m lam (f n) x := by
  by_cases hx : x ∈ Set.range (emb m)
  · obtain ⟨y, rfl⟩ := hx
    rw [localResolvent_apply R emb hemb.injective lam _ y]
    have hcomp : ∀ n, Measurable fun z : X m ↦ f n (emb m z) := fun n ↦
      (hf n).comp hemb.measurable
    have hmonoComp : Monotone fun n ↦ fun z : X m ↦ f n (emb m z) :=
      fun a b hab z ↦ hmono hab (emb m z)
    rw [(R m).kernelSemigroup.p2m_embedded_5e165efdb81ebb50 lam hcomp hmonoComp y]
    exact iSup_congr fun n ↦ (localResolvent_apply R emb hemb.injective lam (f n) y).symm
  · have hzero : ∀ n, localResolvent R emb m lam (f n) x = 0 :=
      fun n ↦ localResolvent_of_notMem R emb m lam (f n) hx
    rw [localResolvent_of_notMem R emb m lam _ hx]
    simp only [hzero, ciSup_const]

section Compatible

variable (iota : ∀ m, X m → X (m + 1))





end Compatible

/-- **The minimal resolvent** of a family of local resolvents: the pointwise supremum of the
transported local kernel resolvents.  Monotonicity in `m`, under which the supremum is an
increasing limit, is the content of `localResolvent_le_succ`. -/
noncomputable def minimalResolvent (lam : ℝ) (f : alpha → ℝ≥0∞) (x : alpha) : ℝ≥0∞ :=
  ⨆ m, localResolvent R emb m lam f x



omit [MeasurableSpace alpha] in
/-- The minimal resolvent is monotone in the observable. -/
theorem minimalResolvent_mono_of_le (hemb : ∀ m, Function.Injective (emb m)) (lam : ℝ)
    {f g : alpha → ℝ≥0∞} (hfg : f ≤ g) (x : alpha) :
    minimalResolvent R emb lam f x ≤ minimalResolvent R emb lam g x :=
  iSup_mono fun m ↦ localResolvent_mono_of_le R emb (hemb m) lam hfg x

/-- The minimal resolvent is continuous along monotone limits of observables. -/
theorem minimalResolvent_iSup (hemb : ∀ m, MeasurableEmbedding (emb m)) (lam : ℝ)
    {f : ℕ → alpha → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) (hmono : Monotone f) (x : alpha) :
    minimalResolvent R emb lam (fun y ↦ ⨆ n, f n y) x =
      ⨆ n, minimalResolvent R emb lam (f n) x := by
  unfold minimalResolvent
  rw [iSup_comm]
  exact iSup_congr fun m ↦ _root_.MarkovProcess.p2m_embedded_b806785ec653a433 R emb (hemb m) lam hf hmono x

/-- The minimal resolvent is measurable in the starting point. -/
theorem measurable_minimalResolvent (hemb : ∀ m, MeasurableEmbedding (emb m)) (lam : ℝ)
    {f : alpha → ℝ≥0∞} (hf : Measurable f) :
    Measurable (minimalResolvent R emb lam f) :=
  Measurable.iSup fun m ↦ measurable_localResolvent R emb (hemb m) lam hf

omit [MeasurableSpace alpha] in
/-- At a positive shift the minimal resolvent of the constant observable one is at most
`1 / lam`. -/
theorem minimalResolvent_one_le (hemb : ∀ m, Function.Injective (emb m))
    {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    minimalResolvent R emb lam (fun _ ↦ 1) x ≤ ENNReal.ofReal lam⁻¹ := by
  refine iSup_le fun m ↦ ?_
  by_cases hx : x ∈ Set.range (emb m)
  · obtain ⟨y, rfl⟩ := hx
    rw [localResolvent_apply R emb (hemb m) lam _ y]
    exact (R m).kernelSemigroup.kernelResolvent_one_le hlam y
  · rw [localResolvent_of_notMem R emb m lam _ hx]
    exact zero_le



section ResolventEquation

variable (iota : ∀ m, X m → X (m + 1))

/-- Each transported resolvent satisfies the resolvent equation. -/
theorem p2m_embedded_8d461c52cdffeee4 {m : ℕ} (hemb : MeasurableEmbedding (emb m))
    {lam mu : ℝ} (hlt : lam < mu) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    localResolvent R emb m lam f x =
      localResolvent R emb m mu f x +
        ENNReal.ofReal (mu - lam) *
          localResolvent R emb m lam (localResolvent R emb m mu f) x := by
  by_cases hx : x ∈ Set.range (emb m)
  · obtain ⟨y, rfl⟩ := hx
    have hinner : (fun z ↦ localResolvent R emb m mu f (emb m z)) =
        (R m).kernelSemigroup.kernelResolvent mu fun z ↦ f (emb m z) := by
      funext z
      exact localResolvent_apply R emb hemb.injective mu f z
    rw [localResolvent_apply R emb hemb.injective lam f y,
      localResolvent_apply R emb hemb.injective mu f y,
      localResolvent_apply R emb hemb.injective lam _ y, hinner]
    exact (R m).kernelSemigroup.p2m_embedded_2c29c39b3a1c7269 hlt
      (hf.comp hemb.measurable) y
  · rw [localResolvent_of_notMem R emb m lam f hx,
      localResolvent_of_notMem R emb m mu f hx,
      localResolvent_of_notMem R emb m lam _ hx]
    simp only [mul_zero, add_zero]

/-- **The composition of two supremum resolvents is the supremum along the diagonal**, as soon
as the transported resolvents are monotone in the index. -/
theorem p2m_embedded_837741bc8cbb97d8 (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {g : alpha → ℝ≥0∞}, Measurable g → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu g y)
    {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu) {f : alpha → ℝ≥0∞} (hf : Measurable f)
    (x : alpha) :
    minimalResolvent R emb lam (minimalResolvent R emb mu f) x =
      ⨆ n, localResolvent R emb n lam (localResolvent R emb n mu f) x := by
  have hgmeas : ∀ k, Measurable (localResolvent R emb k mu f) := fun k ↦
    measurable_localResolvent R emb (hemb k) mu hf
  have hgmono : Monotone fun k ↦ localResolvent R emb k mu f :=
    fun a b hab y ↦ hmono mu hmu hf y hab
  have hrepr : minimalResolvent R emb mu f =
      fun y ↦ ⨆ k, localResolvent R emb k mu f y := rfl
  have hstep : ∀ m, localResolvent R emb m lam
      (fun y ↦ ⨆ k, localResolvent R emb k mu f y) x =
      ⨆ k, localResolvent R emb m lam (localResolvent R emb k mu f) x :=
    fun m ↦ _root_.MarkovProcess.p2m_embedded_b806785ec653a433 R emb (hemb m) lam hgmeas hgmono x
  rw [minimalResolvent, hrepr]
  simp_rw [hstep]
  refine le_antisymm (iSup_le fun m ↦ iSup_le fun k ↦ ?_) (iSup_le fun n ↦ ?_)
  · refine le_iSup_of_le (max m k) ?_
    calc localResolvent R emb m lam (localResolvent R emb k mu f) x
        ≤ localResolvent R emb (max m k) lam (localResolvent R emb k mu f) x :=
          hmono lam hlam (hgmeas k) x (le_max_left m k)
      _ ≤ localResolvent R emb (max m k) lam
            (localResolvent R emb (max m k) mu f) x :=
          localResolvent_mono_of_le R emb (hemb (max m k)).injective lam
            (hgmono (le_max_right m k)) x
  · exact le_iSup_of_le n (le_iSup_of_le n le_rfl)

/-- **The resolvent equation for the supremum of the transported resolvents.**  Each member
satisfies the resolvent equation, and both sides pass to the supremum by monotone convergence.
The only property of the family used is that the transported resolvents are monotone in `m` at
every positive shift. -/
theorem p2m_embedded_f5046fda19eb6f52
    (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {g : alpha → ℝ≥0∞}, Measurable g → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu g y)
    {lam mu : ℝ} (hlam : 0 < lam) (hlt : lam < mu) {f : alpha → ℝ≥0∞} (hf : Measurable f)
    (x : alpha) :
    minimalResolvent R emb lam f x =
      minimalResolvent R emb mu f x +
        ENNReal.ofReal (mu - lam) *
          minimalResolvent R emb lam (minimalResolvent R emb mu f) x := by
  have hmu : 0 < mu := hlam.trans hlt
  have hgmeas : ∀ k, Measurable (localResolvent R emb k mu f) := fun k ↦
    measurable_localResolvent R emb (hemb k) mu hf
  have hgmono : Monotone fun k ↦ localResolvent R emb k mu f :=
    fun a b hab y ↦ hmono mu hmu hf y hab
  have hamono : Monotone fun n ↦ localResolvent R emb n mu f x := hmono mu hmu hf x
  have hbmono : Monotone fun n ↦
      localResolvent R emb n lam (localResolvent R emb n mu f) x := by
    refine monotone_nat_of_le_succ fun n ↦ ?_
    refine le_trans (hmono lam hlam (hgmeas n) x (Nat.le_succ n)) ?_
    exact localResolvent_mono_of_le R emb (hemb (n + 1)).injective lam
      (hgmono (Nat.le_succ n)) x
  have hcmono : Monotone fun n ↦
      ENNReal.ofReal (mu - lam) *
        localResolvent R emb n lam (localResolvent R emb n mu f) x :=
    fun i j hij ↦ mul_le_mul' le_rfl (hbmono hij)
  calc minimalResolvent R emb lam f x = ⨆ n, localResolvent R emb n lam f x := rfl
    _ = ⨆ n, (localResolvent R emb n mu f x +
          ENNReal.ofReal (mu - lam) *
            localResolvent R emb n lam (localResolvent R emb n mu f) x) :=
        iSup_congr fun n ↦
          _root_.MarkovProcess.p2m_embedded_8d461c52cdffeee4 R emb (hemb n) hlt hf x
    _ = (⨆ n, localResolvent R emb n mu f x) +
          ⨆ n, ENNReal.ofReal (mu - lam) *
            localResolvent R emb n lam (localResolvent R emb n mu f) x :=
        (ENNReal.iSup_add_iSup_of_monotone hamono hcmono).symm
    _ = minimalResolvent R emb mu f x +
          ENNReal.ofReal (mu - lam) *
            minimalResolvent R emb lam (minimalResolvent R emb mu f) x := by
        rw [_root_.MarkovProcess.p2m_embedded_837741bc8cbb97d8 R emb hemb hmono hlam hmu hf x,
          ENNReal.mul_iSup, minimalResolvent]



end ResolventEquation

end MarkovProcess


