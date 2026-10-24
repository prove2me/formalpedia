-- Prove2me | solution 1 for AtaBarjesteh23.Workload.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T19:57:31.511467+00:00
-- url     : https://prove2.me/submissions/32ec6afc-10c8-4e26-b8db-d0fe16b797a8

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting
import Definitions.Def_AtaBarjesteh23_Workload_DriftBM
import Definitions.Def_AtaBarjesteh23_Workload_Control
import Theorems.Thm_AtaBarjesteh23_Workload_lemma_1

open MeasureTheory Set Filter Topology

open AtaBarjesteh23.Workload in
theorem solution (M : Model) (hM : M.Standing) (y : ℝ) :
    IsGreatest (range fun x : ℝ => y * x - M.cost x) (M.a / 4 * y ^ 2) ∧
    ∀ x : ℝ, y * x - M.cost x = M.a / 4 * y ^ 2 ↔ x = M.a / 2 * y := by
  have hcost : ∀ x, M.cost x = x ^ 2 / M.a := fun x => (lemma_1 M hM x).2.2.2.2
  obtain ⟨hK, hm, -, -, -, hH, -, -⟩ := hM
  have hmne : M.m ≠ 0 := by
    intro h
    have := hm ⟨0, hK⟩
    rw [h] at this
    simp at this
  have ha : 0 < M.a := by
    have := hH.inv.dotProduct_mulVec_pos hmne
    simpa [Model.a] using this
  have key : ∀ x, y * x - M.cost x = M.a / 4 * y ^ 2 - (x - M.a / 2 * y) ^ 2 / M.a := by
    intro x
    rw [hcost]
    field_simp
    ring
  refine ⟨⟨⟨M.a / 2 * y, ?_⟩, ?_⟩, ?_⟩
  · simp only [key, sub_self]
    ring
  · rintro q ⟨x, rfl⟩
    simp only [key]
    have : 0 ≤ (x - M.a / 2 * y) ^ 2 / M.a := div_nonneg (sq_nonneg _) ha.le
    linarith
  · intro x
    constructor
    · rintro hx
      rw [key] at hx
      have h1 : (x - M.a / 2 * y) ^ 2 / M.a = 0 := by linarith
      rw [div_eq_zero_iff] at h1
      rcases h1 with h1 | h1
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
        linarith
      · linarith
    · rintro rfl
      rw [key]
      ring

