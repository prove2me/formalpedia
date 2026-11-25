-- Prove2me | Definitions.Def_StochLean_Probability_Process_Measurability_Progressive_F001
-- name    : StochLean_Probability_Process_Measurability_Progressive_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:13:32.370246+00:00
-- url     : https://prove2.me/theorems/3d8c29c6-3115-4db6-8f27-94b6e15ba6cb
-- title:
--   StochLean: Probability.Process.Measurability.Progressive F001

import Definitions.Def_StochLean_Probability_Process_Measurability_Progressive_F000
import Definitions.Def_SourceProof_0f8a0101c88cc3ddfc313b0a
import Definitions.Def_SourceProof_2dbf89257579d06e7dcc14c0
import Definitions.Def_SourceProof_5a9e4b64f838761a6226e9d1
import Definitions.Def_SourceProof_cd97db615490c31aef685008

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Progressive measurability from right-continuous paths

For nonnegative real time, a strongly adapted process with right-continuous trajectories is
strongly progressive. The proof uses measurable countable-range right-grid approximations; it
does not strengthen right continuity to continuity.
-/

@[expose] public section

open NNReal TopologicalSpace
open scoped Topology

private noncomputable def cappedRightGrid (i : ℝ≥0) (n : ℕ)
    (t : Set.Iic i) : Set.Iic i :=
  ⟨min i (rightGrid n t), Set.mem_Iic.mpr (min_le_left _ _)⟩
private lemma measurable_cappedRightGrid (i : ℝ≥0) (n : ℕ) :
    Measurable (cappedRightGrid i n) := by
  unfold cappedRightGrid
  exact Measurable.subtype_mk <|
    (measurable_const.min ((_root_.Prove2MeSourceProof.h_cd97db615490c31aef685008 n).comp measurable_subtype_coe))
private lemma tendsto_cappedRightGrid (i : ℝ≥0) (t : Set.Iic i) :
    Filter.Tendsto (fun n ↦ cappedRightGrid i n t) Filter.atTop (𝓝 t) := by
  rw [tendsto_subtype_rng]
  have hc : Filter.Tendsto (fun x : ℝ≥0 ↦ min i x) (𝓝 (t : ℝ≥0))
      (𝓝 (min i (t : ℝ≥0))) :=
    (continuous_const.min continuous_id).continuousAt
  have hcomp := hc.comp (_root_.Prove2MeSourceProof.h_2dbf89257579d06e7dcc14c0 (t : ℝ≥0))
  change Filter.Tendsto (fun n ↦ min i (rightGrid n (t : ℝ≥0))) Filter.atTop
    (𝓝 (min i (t : ℝ≥0))) at hcomp
  simpa only [cappedRightGrid, min_eq_right (Set.mem_Iic.mp t.property)] using hcomp
private lemma countable_range_cappedRightGrid (i : ℝ≥0) (n : ℕ) :
    (Set.range (cappedRightGrid i n)).Countable := by
  have hsub : Set.range (cappedRightGrid i n) ⊆
      {⟨i, Set.mem_Iic.mpr le_rfl⟩} ∪
        Subtype.val ⁻¹' Set.range (rightGrid n) := by
    rintro y ⟨t, rfl⟩
    by_cases h : i ≤ rightGrid n t
    · left
      apply Subtype.ext
      simp [cappedRightGrid, min_eq_left h]
    · right
      exact ⟨t, by simp [cappedRightGrid, min_eq_right (le_of_not_ge h)]⟩
  refine (Set.countable_singleton _).union ?_ |>.mono hsub
  exact (_root_.Prove2MeSourceProof.h_0f8a0101c88cc3ddfc313b0a n).preimage Subtype.val_injective
private lemma le_cappedRightGrid (i : ℝ≥0) (n : ℕ) (t : Set.Iic i) :
    (t : ℝ≥0) ≤ cappedRightGrid i n t := by
  exact le_min t.property (_root_.Prove2MeSourceProof.h_5a9e4b64f838761a6226e9d1 n t)
private lemma tendsto_cappedRightGrid_nhdsWithin (i : ℝ≥0) (t : Set.Iic i) :
    Filter.Tendsto (fun n ↦ ((cappedRightGrid i n t : Set.Iic i) : ℝ≥0)) Filter.atTop
      (nhdsWithin (t : ℝ≥0) (Set.Ici t)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact continuous_subtype_val.continuousAt.tendsto.comp (tendsto_cappedRightGrid i t)
  · exact Filter.Eventually.of_forall fun n ↦ Set.mem_Ici.mpr (le_cappedRightGrid i n t)
private noncomputable def leftGrid (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (Nat.floor (((n + 1 : ℕ) : ℝ≥0) * t) : ℝ≥0) / (n + 1 : ℕ)
private lemma leftGrid_le (n : ℕ) (t : ℝ≥0) : leftGrid n t ≤ t := by
  rw [leftGrid, div_le_iff₀ (by positivity)]
  simpa [mul_comm] using
    Nat.floor_le (show (0 : ℝ≥0) ≤ ((n + 1 : ℕ) : ℝ≥0) * t by positivity)
private lemma measurable_leftGrid (n : ℕ) : Measurable (leftGrid n) := by
  unfold leftGrid
  fun_prop
private lemma countable_range_leftGrid (n : ℕ) :
    (Set.range (leftGrid n)).Countable := by
  refine (Set.countable_range (fun k : ℕ ↦ (k : ℝ≥0) / (n + 1 : ℕ))).mono ?_
  rintro y ⟨t, rfl⟩
  exact ⟨Nat.floor (((n + 1 : ℕ) : ℝ≥0) * t), rfl⟩
private lemma lt_leftGrid_add (n : ℕ) (t : ℝ≥0) :
    t < leftGrid n t + 1 / (n + 1 : ℕ) := by
  rw [leftGrid, ← add_div]
  rw [lt_div_iff₀ (by positivity)]
  simpa [mul_comm] using Nat.lt_floor_add_one (((n + 1 : ℕ) : ℝ≥0) * t)
private lemma tendsto_leftGrid (t : ℝ≥0) :
    Filter.Tendsto (fun n ↦ leftGrid n t) Filter.atTop (𝓝 t) := by
  have hδ : Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ≥0) / ((n : ℝ≥0) + 1))
      Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlower : Filter.Tendsto
      (fun n : ℕ ↦ t - (1 : ℝ≥0) / ((n : ℝ≥0) + 1)) Filter.atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.sub hδ
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
    (fun n ↦ by
      apply tsub_le_iff_right.mpr
      simpa [Nat.cast_add, Nat.cast_one] using (lt_leftGrid_add n t).le)
    (fun n ↦ leftGrid_le n t)
private lemma tendsto_leftGrid_nhdsWithin (t : ℝ≥0) :
    Filter.Tendsto (fun n ↦ leftGrid n t) Filter.atTop (nhdsWithin t (Set.Iic t)) := by
  exact tendsto_nhdsWithin_iff.mpr ⟨tendsto_leftGrid t,
    Filter.Eventually.of_forall fun n ↦ Set.mem_Iic.mpr (leftGrid_le n t)⟩
private noncomputable def leftGridOnHorizon (i : ℝ≥0) (n : ℕ)
    (t : Set.Iic i) : Set.Iic i :=
  ⟨leftGrid n t, (leftGrid_le n t).trans t.property⟩
private lemma measurable_leftGridOnHorizon (i : ℝ≥0) (n : ℕ) :
    Measurable (leftGridOnHorizon i n) := by
  unfold leftGridOnHorizon
  exact Measurable.subtype_mk ((measurable_leftGrid n).comp measurable_subtype_coe)
private lemma countable_range_leftGridOnHorizon (i : ℝ≥0) (n : ℕ) :
    (Set.range (leftGridOnHorizon i n)).Countable := by
  apply ((countable_range_leftGrid n).preimage Subtype.val_injective).mono
  rintro y ⟨t, rfl⟩
  exact ⟨t, rfl⟩
namespace MeasureTheory

namespace StronglyAdapted

end StronglyAdapted

end MeasureTheory


