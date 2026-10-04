-- Prove2me | solution 1 for AssumptionsOfPhysics.isOpen_real_eq_iUnion_intervals
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T03:43:59.076971+00:00
-- url     : https://prove2.me/submissions/0c91ea6c-2076-49bb-9440-fb671ececc4c

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_PropertiesQuantities

set_option autoImplicit false

open AssumptionsOfPhysics in
theorem solution (U : Set ℝ)
    (hU : @IsOpen ℝ (TopologicalSpace.generateFrom
      {S : Set ℝ | ∃ a b : ℚ, S = Set.Ioo (a : ℝ) (b : ℝ)}) U) :
    ∃ a b : ℕ → EReal, U = ⋃ i, {x : ℝ | a i < (x : EReal) ∧ (x : EReal) < b i} := by
  classical
  have hU' : IsOpen U := by
    change TopologicalSpace.GenerateOpen _ U at hU
    induction hU with
    | basic s hs =>
      obtain ⟨a, b, rfl⟩ := hs
      exact isOpen_Ioo
    | univ => exact isOpen_univ
    | inter s t _ _ hs ht => exact hs.inter ht
    | sUnion S _ ih => exact isOpen_sUnion ih
  obtain ⟨e, he⟩ := exists_surjective_nat (ℚ × ℚ)
  refine ⟨fun i => if Set.Ioo ((e i).1 : ℝ) ((e i).2 : ℝ) ⊆ U then (((e i).1 : ℝ) : EReal) else ⊤,
    fun i => (((e i).2 : ℝ) : EReal), ?_⟩
  ext x
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · intro hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU' x hx
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x - ε < x by linarith)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show x < x + ε by linarith)
    obtain ⟨i, hi⟩ := he (q, r)
    have hsub : Set.Ioo (q : ℝ) (r : ℝ) ⊆ U := by
      intro y hy
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hy.1, hy.2]
    refine ⟨i, ?_, ?_⟩
    · rw [hi]
      simp only [hsub, if_true]
      exact EReal.coe_lt_coe_iff.2 hq2
    · rw [hi]
      exact EReal.coe_lt_coe_iff.2 hr1
  · rintro ⟨i, h1, h2⟩
    by_cases hs : Set.Ioo ((e i).1 : ℝ) ((e i).2 : ℝ) ⊆ U
    · simp only [hs, if_true] at h1
      exact hs ⟨EReal.coe_lt_coe_iff.1 h1, EReal.coe_lt_coe_iff.1 h2⟩
    · simp only [hs, if_false] at h1
      exact absurd h1 (not_top_lt)
