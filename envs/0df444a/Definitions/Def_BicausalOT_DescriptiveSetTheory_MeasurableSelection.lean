-- Prove2me | Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
-- name    : BicausalOT_DescriptiveSetTheory_MeasurableSelection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:06:55.318188+00:00
-- url     : https://prove2.me/theorems/527bb6db-bc46-5432-8cd3-b39a8ee4e5f3
-- title:
--   Measurable Selection
-- statement:
--   Definitions and structural lemmas for Measurable Selection, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean

import Mathlib
set_option autoImplicit false
open Metric Set Filter Topology TopologicalSpace
namespace MeasurableSelection
noncomputable def firstIdx (p : ℕ → Prop) (h : ∃ n, p n) : ℕ :=
  @Nat.find p (Classical.decPred p) h
theorem firstIdx_spec {p : ℕ → Prop} (h : ∃ n, p n) : p (firstIdx p h) := by
  letI := Classical.decPred p
  exact Nat.find_spec h
theorem firstIdx_eq_iff {p : ℕ → Prop} (h : ∃ n, p n) {k : ℕ} :
    firstIdx p h = k ↔ p k ∧ ∀ j < k, ¬p j := by
  letI := Classical.decPred p
  exact Nat.find_eq_iff h
variable {α : Type*} [MeasurableSpace α]
theorem measurable_firstIdx {p : α → ℕ → Prop} (hex : ∀ a, ∃ n, p a n)
    (hm : ∀ k, MeasurableSet {a | p a k}) :
    Measurable fun a => firstIdx (p a) (hex a) := by
  refine measurable_to_countable' fun k => ?_
  have hset : (fun a => firstIdx (p a) (hex a)) ⁻¹' {k} =
      {a | p a k} ∩ ⋂ (j : ℕ) (_ : j < k), {a | p a j}ᶜ := by
    ext a
    simp only [mem_preimage, mem_singleton_iff, firstIdx_eq_iff, mem_inter_iff,
      mem_ofPred_eq, mem_iInter, mem_compl_iff]
  rw [hset]
  exact (hm k).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hm j).compl)
variable {Y : Type*} [MetricSpace Y] {Φ : α → Set Y} {u : ℕ → Y}
omit [MeasurableSpace α] in
/-- Base step: some `u k` comes within distance `1` of the nonempty set `Φ a`. -/
theorem base_exists (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty) (a : α) :
    ∃ k, (Φ a ∩ ball (u k) 1).Nonempty := by
  obtain ⟨y, hy⟩ := hne a
  obtain ⟨k, hk⟩ := hu.exists_dist_lt y one_pos
  exact ⟨k, y, hy, mem_ball.mpr hk⟩
noncomputable def baseFun (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty) : α → ℕ :=
  fun a => firstIdx _ (base_exists hu hne a)
omit [MeasurableSpace α] in
theorem baseFun_spec (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty) (a : α) :
    (Φ a ∩ ball (u (baseFun hu hne a)) 1).Nonempty :=
  firstIdx_spec (base_exists hu hne a)
theorem baseFun_measurable (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty)
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty}) :
    Measurable (baseFun hu hne) :=
  measurable_firstIdx (base_exists hu hne) fun _ => hΦ _ isOpen_ball
omit [MeasurableSpace α] in
/-- Refinement step, existence: if `Φ a` meets `ball (u (g a)) r`, then by density some
`u k` with `k` least comes within `r'` of a point of `Φ a ∩ ball (u (g a)) r`. -/
theorem step_exists (hu : DenseRange u) {g : α → ℕ} {r : ℝ}
    (hg : ∀ a, (Φ a ∩ ball (u (g a)) r).Nonempty) {r' : ℝ} (hr' : 0 < r') (a : α) :
    ∃ k, (Φ a ∩ (ball (u k) r' ∩ ball (u (g a)) r)).Nonempty := by
  obtain ⟨y, hyΦ, hyb⟩ := hg a
  obtain ⟨k, hk⟩ := hu.exists_dist_lt y hr'
  exact ⟨k, y, hyΦ, mem_ball.mpr hk, hyb⟩
theorem step_measurableSet
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty})
    {g : α → ℕ} (hgm : Measurable g) (r r' : ℝ) (k : ℕ) :
    MeasurableSet {a | (Φ a ∩ (ball (u k) r' ∩ ball (u (g a)) r)).Nonempty} := by
  have hset : {a | (Φ a ∩ (ball (u k) r' ∩ ball (u (g a)) r)).Nonempty} =
      ⋃ j : ℕ, {a | g a = j} ∩ {a | (Φ a ∩ (ball (u k) r' ∩ ball (u j) r)).Nonempty} := by
    ext a
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · exact fun h => ⟨g a, rfl, h⟩
    · rintro ⟨j, rfl, h⟩
      exact h
  rw [hset]
  exact MeasurableSet.iUnion fun j =>
    (hgm (measurableSet_singleton j)).inter (hΦ _ (isOpen_ball.inter isOpen_ball))
noncomputable def stepFun (hu : DenseRange u) {g : α → ℕ} {r : ℝ}
    (hg : ∀ a, (Φ a ∩ ball (u (g a)) r).Nonempty) {r' : ℝ} (hr' : 0 < r') : α → ℕ :=
  fun a => firstIdx _ (step_exists hu hg hr' a)
omit [MeasurableSpace α] in
theorem stepFun_spec (hu : DenseRange u) {g : α → ℕ} {r : ℝ}
    (hg : ∀ a, (Φ a ∩ ball (u (g a)) r).Nonempty) {r' : ℝ} (hr' : 0 < r') (a : α) :
    (Φ a ∩ (ball (u (stepFun hu hg hr' a)) r' ∩ ball (u (g a)) r)).Nonempty :=
  firstIdx_spec (step_exists hu hg hr' a)
theorem stepFun_measurable (hu : DenseRange u)
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty})
    {g : α → ℕ} {r : ℝ} (hg : ∀ a, (Φ a ∩ ball (u (g a)) r).Nonempty)
    {r' : ℝ} (hr' : 0 < r') (hgm : Measurable g) :
    Measurable (stepFun hu hg hr') :=
  measurable_firstIdx (step_exists hu hg hr') fun k => step_measurableSet hΦ hgm r r' k
noncomputable def approx (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty)
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty}) :
    (n : ℕ) →
      {g : α → ℕ // Measurable g ∧ ∀ a, (Φ a ∩ ball (u (g a)) ((1 / 2 : ℝ) ^ n)).Nonempty}
  | 0 =>
    ⟨baseFun hu hne, baseFun_measurable hu hne hΦ, fun a => by
      simpa using baseFun_spec hu hne a⟩
  | n + 1 =>
    ⟨stepFun hu (approx hu hne hΦ n).2.2 (pow_pos one_half_pos (n + 1)),
      stepFun_measurable hu hΦ (approx hu hne hΦ n).2.2 (pow_pos one_half_pos (n + 1))
        (approx hu hne hΦ n).2.1,
      fun a =>
        Exists.imp (fun _ hy => ⟨hy.1, hy.2.1⟩)
          (stepFun_spec hu (approx hu hne hΦ n).2.2 (pow_pos one_half_pos (n + 1)) a)⟩
noncomputable def approxFun (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty)
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty})
    (n : ℕ) (a : α) : Y :=
  u ((approx hu hne hΦ n).1 a)
section Limit
variable [MeasurableSpace Y] [BorelSpace Y]
end Limit
end MeasurableSelection


