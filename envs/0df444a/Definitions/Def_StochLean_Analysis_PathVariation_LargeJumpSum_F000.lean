-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_LargeJumpSum_F000
-- name    : StochLean_Analysis_PathVariation_LargeJumpSum_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:32:08.119871+00:00
-- url     : https://prove2.me/theorems/9dd0ece8-735c-5a53-9888-0e222f705215
-- title:
--   StochLean: Analysis.PathVariation.LargeJumpSum F000

import Definitions.Def_StochLean_Analysis_PathVariation_CompletedSums_F001
import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_1c5616a125ac7367f7f20567
import Definitions.Def_SourceProof_203c8143f8646ca99211fe57
import Definitions.Def_SourceProof_59980e478d16e5d17042fad7
import Definitions.Def_SourceProof_ecbfe96d629906d63863658f
import Definitions.Def_SourceProof_fb98cafaf4269dae3b77bad4
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Data.Finset.Max
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual cumulative large jumps of a cadlag path

The sums are the ordinary `tsum` over the actual positive-time interval.
On each compact horizon, cadlag large-jump finiteness identifies them with
an existing finite cumulative step sum. This proves path regularity and
the exact jumps without any global absolute-summability hypothesis.

The signed sum has compact variation bounded by the actual absolute jump
sum. Time zero is excluded from both sums, regardless of the original
initial value; the positive-time residual jumps have norm at most the
threshold. No adaptedness, measurability, stopping-time, or integrability
claim is made in this deterministic module.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace StochLean

private theorem cumulative_eq_finite_steps {g : ℝ≥0 → ℝ} {T t : ℝ≥0}
    (s : Finset ℝ≥0) (hp : ∀ r ∈ s, 0 < r)
    (hs : ∀ r, 0 < r → r ≤ T → r ∉ s → g r = 0) (ht : t ≤ T) :
    (∑' r : Ioc 0 t, g r) = ∑ r ∈ s, if r ≤ t then g r else 0 := by
  classical
  rw [tsum_subtype]
  calc
    (∑' r, (Ioc 0 t).indicator g r) = ∑ r ∈ s, (Ioc 0 t).indicator g r := by
      apply tsum_eq_sum
      intro r hr
      by_cases hrt : r ∈ Ioc 0 t
      · rw [indicator_of_mem hrt]
        exact hs r hrt.1 (hrt.2.trans ht) hr
      · exact indicator_of_notMem hrt g
    _ = _ := Finset.sum_congr rfl fun r hr ↦ by
      simp only [indicator_apply, mem_Ioc, hp r hr, true_and]
private theorem locally_finite_summable_abs {g : ℝ≥0 → ℝ}
    (hf : ∀ T : ℝ≥0, {t : ℝ≥0 | 0 < t ∧ t ≤ T ∧ g t ≠ 0}.Finite) (T : ℝ≥0) :
    Summable (fun t : Ioc 0 T ↦ |g t|) := by
  apply summable_of_hasFiniteSupport
  apply ((hf T).preimage (f := fun t : Ioc 0 T ↦ (t : ℝ≥0))
    Subtype.val_injective.injOn).subset
  intro t ht
  exact ⟨t.2.1, t.2.2, abs_ne_zero.mp ht⟩
private theorem cadlag_cumulative_of_locally_finite {g : ℝ≥0 → ℝ}
    (hf : ∀ T : ℝ≥0, {t : ℝ≥0 | 0 < t ∧ t ≤ T ∧ g t ≠ 0}.Finite) :
    IsCadlagPath (fun t : ℝ≥0 ↦ ∑' r : Ioc 0 t, g r) := by
  classical
  have hlocal (t : ℝ≥0) : ∃ B : ℝ≥0 → ℝ, IsCadlagPath B ∧
      (∑' r : Ioc 0 t, g r) = B t ∧
        (fun u : ℝ≥0 ↦ ∑' r : Ioc 0 u, g r) =ᶠ[𝓝 t] B := by
    let s := (hf (t + 1)).toFinset
    have hp : ∀ r ∈ s, 0 < r := fun r hr ↦ ((hf (t + 1)).mem_toFinset.mp hr).1
    have hs : ∀ r, 0 < r → r ≤ t + 1 → r ∉ s → g r = 0 := by
      intro r hr hrT hrs
      by_contra hgr
      exact hrs ((hf (t + 1)).mem_toFinset.mpr ⟨hr, hrT, hgr⟩)
    let B : ℝ≥0 → ℝ := fun u ↦ ∑ r ∈ s, if r ≤ u then g r else 0
    refine ⟨B, _root_.Prove2MeSourceProof.h_203c8143f8646ca99211fe57 s (fun r u ↦ if r ≤ u then g r else 0)
      (fun r _ ↦ _root_.Prove2MeSourceProof.h_1c5616a125ac7367f7f20567 r (g r)),
      cumulative_eq_finite_steps s hp hs (le_add_of_nonneg_right zero_le_one), ?_⟩
    filter_upwards [Iio_mem_nhds (lt_add_one t)] with u hu
    exact cumulative_eq_finite_steps s hp hs (show u < t + 1 from hu).le
  constructor
  · intro t
    obtain ⟨B, hc, he, hnear⟩ := hlocal t
    change Tendsto (fun u : ℝ≥0 ↦ ∑' r : Ioc 0 u, g r) (𝓝[≥] t)
      (𝓝 (∑' r : Ioc 0 t, g r))
    rw [he]
    exact (hc.1 t).congr' (hnear.symm.filter_mono nhdsWithin_le_nhds)
  · intro t ht
    obtain ⟨B, hc, _, hnear⟩ := hlocal t
    obtain ⟨L, hL⟩ := hc.2 t ht
    exact ⟨L, hL.congr' (hnear.symm.filter_mono nhdsWithin_le_nhds)⟩
private theorem cumulative_sub_leftLim_of_locally_finite {g : ℝ≥0 → ℝ}
    (hf : ∀ T : ℝ≥0, {t : ℝ≥0 | 0 < t ∧ t ≤ T ∧ g t ≠ 0}.Finite)
    {t : ℝ≥0} (ht : 0 < t) :
    (∑' r : Ioc 0 t, g r) - leftLim (fun u : ℝ≥0 ↦ ∑' r : Ioc 0 u, g r) t = g t := by
  classical
  let s := (hf t).toFinset
  have hp : ∀ r ∈ s, 0 < r := fun r hr ↦ ((hf t).mem_toFinset.mp hr).1
  have hs : ∀ r, 0 < r → r ≤ t → r ∉ s → g r = 0 := by
    intro r hr hrt hrs
    by_contra hgr
    exact hrs ((hf t).mem_toFinset.mpr ⟨hr, hrt, hgr⟩)
  let B : ℝ≥0 → ℝ := fun u ↦ ∑ r ∈ s, if r ≤ u then g r else 0
  have hcB : IsCadlagPath B := _root_.Prove2MeSourceProof.h_203c8143f8646ca99211fe57 s
    (fun r u ↦ if r ≤ u then g r else 0) (fun r _ ↦ _root_.Prove2MeSourceProof.h_1c5616a125ac7367f7f20567 r (g r))
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hleft : leftLim (fun u : ℝ≥0 ↦ ∑' r : Ioc 0 u, g r) t = leftLim B t := by
    apply leftLim_eq_of_tendsto
    apply (tendsto_leftLim_of_tendsto (hcB.2 t ht.ne')).congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (cumulative_eq_finite_steps s hp hs (show u < t from hu).le).symm
  rw [hleft, cumulative_eq_finite_steps s hp hs le_rfl]
  have hj : B t - leftLim B t = ∑ r ∈ s, if r = t then g r else 0 := by
    have h := _root_.Prove2MeSourceProof.h_ecbfe96d629906d63863658f s
      (fun r (_ : Unit) ↦ (r : WithTop ℝ≥0)) (fun r (_ : Unit) ↦ g r) t ()
    simpa only [jumpProcess, Pi.sub_apply, leftLimitProcess, if_neg ht.ne',
      indicator_apply, mem_ofPred_eq, WithTop.coe_le_coe, WithTop.coe_eq_coe] using h
  rw [hj]
  by_cases hts : t ∈ s
  · rw [Finset.sum_eq_single_of_mem t hts]
    · simp only [ite_true]
    · intro r _ hrt
      exact if_neg hrt
  · calc
      _ = 0 := Finset.sum_eq_zero fun r hr ↦
        if_neg (fun (he : r = t) ↦ hts (he ▸ hr))
      _ = g t := (hs t ht le_rfl hts).symm
private theorem variation_cumulative_le_abs_sum_of_locally_finite {g : ℝ≥0 → ℝ}
    (hf : ∀ T : ℝ≥0, {t : ℝ≥0 | 0 < t ∧ t ≤ T ∧ g t ≠ 0}.Finite) (T : ℝ≥0) :
    eVariationOn (fun t : ℝ≥0 ↦ ∑' r : Ioc 0 t, g r) (Icc 0 T) ≤
      ENNReal.ofReal (∑' r : Ioc 0 T, |g r|) := by
  classical
  let s := (hf T).toFinset
  have hp : ∀ r ∈ s, 0 < r := fun r hr ↦ ((hf T).mem_toFinset.mp hr).1
  have hb : ∀ r ∈ s, r ≤ T := fun r hr ↦ ((hf T).mem_toFinset.mp hr).2.1
  have hs : ∀ r, 0 < r → r ≤ T → r ∉ s → g r = 0 := by
    intro r hr hrt hrs
    by_contra hgr
    exact hrs ((hf T).mem_toFinset.mpr ⟨hr, hrt, hgr⟩)
  have he (t : ℝ≥0) (ht : t ≤ T) : (∑' r : Ioc 0 t, g r) =
      cumulativeStepSum (fun r : s ↦ (r : ℝ≥0)) (fun r ↦ g r) t := by
    rw [cumulative_eq_finite_steps s hp hs ht]
    exact (Finset.sum_attach s (fun r ↦ if r ≤ t then g r else 0)).symm
  have heabs : (∑' r : Ioc 0 T, |g r|) = ∑ r : s, |g r| := by
    rw [cumulative_eq_finite_steps (g := fun r ↦ |g r|) (T := T) (t := T) s hp
      (fun r hr hrt hrs ↦ by rw [hs r hr hrt hrs, abs_zero]) le_rfl]
    calc
      _ = ∑ r ∈ s, |g r| := Finset.sum_congr rfl fun r hr ↦ if_pos (hb r hr)
      _ = _ := (Finset.sum_attach s (fun r ↦ |g r|)).symm
  rw [eVariationOn.congr (fun t ht ↦ he t ht.2), heabs]
  exact _root_.Prove2MeSourceProof.h_59980e478d16e5d17042fad7 (fun r : s ↦ (r : ℝ≥0)) (fun r ↦ g r) _
end StochLean

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {b : ℝ}

private theorem finite_support_large_jump_weights (hX : IsCadlagPath (X · ω)) (hb : 0 < b)
    (T : ℝ≥0) :
    {t : ℝ≥0 | 0 < t ∧ t ≤ T ∧
      (if b < ‖jumpProcess X t ω‖ then jumpProcess X t ω else 0) ≠ 0}.Finite := by
  apply ((_root_.Prove2MeSourceProof.h_fb98cafaf4269dae3b77bad4 hX) T hb).subset
  rintro t ⟨ht, htT, hne⟩
  refine ⟨ht, htT, ?_⟩
  by_contra hj
  exact hne (if_neg hj)
private theorem finite_support_abs_large_jump_weights (hX : IsCadlagPath (X · ω)) (hb : 0 < b)
    (T : ℝ≥0) :
    {t : ℝ≥0 | 0 < t ∧ t ≤ T ∧
      (if b < ‖jumpProcess X t ω‖ then ‖jumpProcess X t ω‖ else 0) ≠ 0}.Finite := by
  apply ((_root_.Prove2MeSourceProof.h_fb98cafaf4269dae3b77bad4 hX) T hb).subset
  rintro t ⟨ht, htT, hne⟩
  refine ⟨ht, htT, ?_⟩
  by_contra hj
  exact hne (if_neg hj)
end ProbabilityTheory


