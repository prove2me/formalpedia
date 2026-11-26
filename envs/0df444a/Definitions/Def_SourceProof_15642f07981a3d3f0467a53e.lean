-- Prove2me | Definitions.Def_SourceProof_15642f07981a3d3f0467a53e
-- name    : SourceProof_15642f07981a3d3f0467a53e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T22:54:08.038152+00:00
-- url     : https://prove2.me/theorems/fedf4adf-4f6b-52a0-b0a6-63dcf68db3bb
-- title:
--   StochLean source theorem: ProbabilityTheory.frechetTaylorError_limit_eq_jump_series

import Definitions.Def_StochLean_Probability_Process_Partition_VectorTaylorSums_F000
import Definitions.Def_SourceProof_203c8143f8646ca99211fe57
import Definitions.Def_SourceProof_30d0c59bde2d1c0616100b0f
import Definitions.Def_SourceProof_3b9e1eacb18faa84cc0222f4
import Definitions.Def_SourceProof_51c0da11e7e46e13ea7b46dd
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_7ba09845626a27514db15155
import Definitions.Def_SourceProof_889a358c870927dae89b0906
import Definitions.Def_SourceProof_889cc5878c88eebb9dbc02bf
import Definitions.Def_SourceProof_9183846313e90de3d6561ee0
import Definitions.Def_SourceProof_944fa57bc3b71053cbab118a
import Definitions.Def_SourceProof_a307e422895411519841ce97
import Definitions.Def_SourceProof_c3a38a53524388b4ac4c79ee
import Definitions.Def_SourceProof_ef39e32da25cd087940fc673
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Filter.Finite
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.UniformSpace.UniformApproximation

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Identifying vector stochastic Taylor errors on one common event

One uniform subsequence of the sum of the original coordinate raw-square
approximations bounds vector energy. A nested error subsequence then identifies
every finite-time limit with the actual summable Frechet jump correction.
-/

@[expose] public section

open MeasureTheory Filter Set Finset StochLean
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
  {X : ι → ℝ≥0 → Ω → ℝ} {Z : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_15642f07981a3d3f0467a53e
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P)
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P)
    (hE : TendstoUCP P (fun n ↦ (π n).frechetTaylorErrorProcess f X) atTop Z) :
    Indistinguishable Z (fun t ω ↦ ∑' s : Ioc 0 t,
      frechetSecondOrderRemainder f (fun i ↦ leftLimitProcess (X i) s ω)
        (fun i ↦ X i s ω)) P := by
  have hUQ := _root_.Prove2MeSourceProof.h_ef39e32da25cd087940fc673 univ
    (fun i _ ↦ (_root_.Prove2MeSourceProof.h_c3a38a53524388b4ac4c79ee (hX i)) hF hπ)
  obtain ⟨k, hk, hkU⟩ := (_root_.Prove2MeSourceProof.h_944fa57bc3b71053cbab118a hUQ)
  obtain ⟨l, hl, hlU⟩ := (_root_.Prove2MeSourceProof.h_944fa57bc3b71053cbab118a ((_root_.Prove2MeSourceProof.h_a307e422895411519841ce97 hE) hk.tendsto_atTop))
  have hcQ : ∀ᵐ ω ∂P, ∀ i, ProbabilityTheory.IsCadlagPath ((hX i).quadraticVariation hF · ω) :=
    ae_all_iff.mpr (fun i ↦ (_root_.Prove2MeSourceProof.h_51c0da11e7e46e13ea7b46dd (hX i)) hF)
  filter_upwards [hkU, hlU, hπ, _root_.Prove2MeSourceProof.h_889cc5878c88eebb9dbc02bf (fun i ↦ (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 (hX i))),
    hcQ, _root_.Prove2MeSourceProof.h_30d0c59bde2d1c0616100b0f hX hF]
    with ω hQu hEu hπω hx hQpaths hsq
  have hm : Tendsto (fun n ↦ ((π (k (l n))).mesh ω : ℝ)) atTop (𝓝 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp
      ((hπω.2.comp hk.tendsto_atTop).comp hl.tendsto_atTop)
  have hQω : ProbabilityTheory.IsCadlagPath (fun s ↦ ∑ i, (hX i).quadraticVariation hF s ω) :=
    _root_.Prove2MeSourceProof.h_203c8143f8646ca99211fe57 univ (fun i s ↦ (hX i).quadraticVariation hF s ω)
      (fun i _ ↦ hQpaths i)
  intro t
  have hT : ∀ᶠ n in atTop, t ≤ (π (k (l n))).terminal ω :=
    ((hπω.1.comp hk.tendsto_atTop).comp hl.tendsto_atTop).eventually (eventually_ge_atTop t)
  have hQ : TendstoUniformlyOn
      (fun n s ↦ ∑ i, (X i 0 ω ^ 2 + StochLean.quadraticVariationSum ((π (k (l n))).path ω)
        (fun u ↦ X i (min u s) ω)))
      (fun s ↦ ∑ i, (hX i).quadraticVariation hF s ω) atTop (Icc 0 t) := by
    simpa only [Finset.sum_apply, ProbabilityTheory.StoppingTimePartition.quadraticVariationSumProcess] using
      (_root_.Prove2MeSourceProof.h_9183846313e90de3d6561ee0.mp ((hQu t).comp hl.tendsto_atTop))
  obtain ⟨B, hB, hb⟩ := _root_.Prove2MeSourceProof.h_889a358c870927dae89b0906
    (fun n ↦ (π (k (l n))).path ω) (x := fun s i ↦ X i s ω) hQω hQ
  have hleft (s : Ioc 0 t) : Function.leftLim (fun u i ↦ X i u ω) s =
      fun i ↦ ProbabilityTheory.leftLimitProcess (X i) s ω := by
    rw [(_root_.Prove2MeSourceProof.h_3b9e1eacb18faa84cc0222f4 hx)]
    funext i
    simp only [ProbabilityTheory.leftLimitProcess, if_neg (ne_of_gt s.2.1)]
  have hj (s : Ioc 0 t) : (fun i ↦ X i s ω) - Function.leftLim (fun u i ↦ X i u ω) s =
      fun i ↦ ProbabilityTheory.jumpProcess (X i) s ω := by rw [hleft]; rfl
  have hs : Summable (fun s : Ioc 0 t ↦
      ‖(fun i ↦ X i s ω) - Function.leftLim (fun u i ↦ X i u ω) s‖ ^ 2) := by
    simpa only [hj] using hsq t
  have hd := _root_.Prove2MeSourceProof.h_7ba09845626a27514db15155
    (fun n ↦ (π (k (l n))).path ω) hx hf hm hT hB
    (hb.mono (fun _ hn ↦ hn t ⟨bot_le, le_rfl⟩)) hs
  have he := (_root_.Prove2MeSourceProof.h_9183846313e90de3d6561ee0.mp (hEu t)).tendsto_at
    (show t ∈ Icc 0 t from ⟨bot_le, le_rfl⟩)
  simpa only [hleft] using tendsto_nhds_unique he hd
end ProbabilityTheory


