-- Prove2me | Definitions.Def_SourceProof_1cce7685e72bf317570bfd3c
-- name    : SourceProof_1cce7685e72bf317570bfd3c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:46:55.501844+00:00
-- url     : https://prove2.me/theorems/b46f89e9-1bd9-4b4e-94ee-fe05048d2e88
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticTaylorError_limit_eq_jump_series

import Definitions.Def_StochLean_Probability_Process_Partition_SquareSums_F000
import Definitions.Def_StochLean_Probability_Process_Partition_TaylorSums_F000
import Definitions.Def_SourceProof_2a0294735f59af179c5d8895
import Definitions.Def_SourceProof_472bb0fb2e5ea3f0d733b6e5
import Definitions.Def_SourceProof_51c0da11e7e46e13ea7b46dd
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_9183846313e90de3d6561ee0
import Definitions.Def_SourceProof_944fa57bc3b71053cbab118a
import Definitions.Def_SourceProof_a307e422895411519841ce97
import Definitions.Def_SourceProof_bfe53c0f4ad1412df776a314
import Definitions.Def_SourceProof_c3a38a53524388b4ac4c79ee
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Filter.Finite
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.UniformSpace.UniformApproximation

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Identifying cadlag stochastic Taylor-error limits with the actual jump series

The raw bracket supplies bounded partial square sums on a nested uniform
subsequence. The deterministic cadlag theorem applies on one common event
at every finite time. No regularity or measurability of the proposed limit
process needs to be separately assumed.
-/

@[expose] public section

open MeasureTheory Filter Set StochLean
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Z : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_1cce7685e72bf317570bfd3c
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P)
    (hE : TendstoUCP P (fun n ↦ (π n).quadraticTaylorErrorProcess f X) atTop Z) :
    Indistinguishable Z (fun t ω ↦ ∑' s : Ioc 0 t,
      (f (X s ω) - f (leftLimitProcess X s ω) -
        deriv f (leftLimitProcess X s ω) * jumpProcess X s ω -
        deriv (deriv f) (leftLimitProcess X s ω) / 2 * (jumpProcess X s ω) ^ 2)) P := by
  obtain ⟨k, hk, hkU⟩ :=
    (_root_.Prove2MeSourceProof.h_944fa57bc3b71053cbab118a ((_root_.Prove2MeSourceProof.h_c3a38a53524388b4ac4c79ee hX) hF hπ))
  obtain ⟨l, hl, hlU⟩ := (_root_.Prove2MeSourceProof.h_944fa57bc3b71053cbab118a ((_root_.Prove2MeSourceProof.h_a307e422895411519841ce97 hE) hk.tendsto_atTop))
  filter_upwards [hkU, hlU, hπ, (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX),
    (_root_.Prove2MeSourceProof.h_51c0da11e7e46e13ea7b46dd hX) hF, (_root_.Prove2MeSourceProof.h_472bb0fb2e5ea3f0d733b6e5 hX) hF]
    with ω hQu hEu hπω hx hQω hsq
  have hm : Tendsto (fun n ↦ ((π (k (l n))).mesh ω : ℝ)) atTop (𝓝 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp
      ((hπω.2.comp hk.tendsto_atTop).comp hl.tendsto_atTop)
  intro t
  have hT : ∀ᶠ n in atTop, t ≤ (π (k (l n))).terminal ω :=
    ((hπω.1.comp hk.tendsto_atTop).comp hl.tendsto_atTop).eventually (eventually_ge_atTop t)
  have hQ : TendstoUniformlyOn
      (fun n s ↦ X 0 ω ^ 2 + StochLean.quadraticVariationSum ((π (k (l n))).path ω)
        (fun u ↦ X (min u s) ω))
      (hX.quadraticVariation hF · ω) atTop (Icc 0 t) :=
    _root_.Prove2MeSourceProof.h_9183846313e90de3d6561ee0.mp ((hQu t).comp hl.tendsto_atTop)
  obtain ⟨B, hB, hb⟩ := _root_.Prove2MeSourceProof.h_2a0294735f59af179c5d8895
    (fun n ↦ (π (k (l n))).path ω) (x := (X · ω)) hQω hQ
  have hj (s : Ioc 0 t) : ProbabilityTheory.leftLimitProcess X s ω = Function.leftLim (X · ω) s := by
    simp only [ProbabilityTheory.leftLimitProcess, if_neg (ne_of_gt s.2.1)]
  have hs : Summable (fun s : Ioc 0 t ↦ (X s ω - Function.leftLim (X · ω) s) ^ 2) := by
    simpa only [ProbabilityTheory.jumpProcess, Pi.sub_apply, hj] using hsq t
  have hd := _root_.Prove2MeSourceProof.h_bfe53c0f4ad1412df776a314
    (fun n ↦ (π (k (l n))).path ω) hx hf hm hT hB
    (hb.mono (fun _ hn ↦ hn t ⟨bot_le, le_rfl⟩)) hs
  have he := (_root_.Prove2MeSourceProof.h_9183846313e90de3d6561ee0.mp (hEu t)).tendsto_at
    (show t ∈ Icc 0 t from ⟨bot_le, le_rfl⟩)
  simpa only [ProbabilityTheory.jumpProcess, Pi.sub_apply, hj] using tendsto_nhds_unique he hd
end IsSemimartingale

end ProbabilityTheory


