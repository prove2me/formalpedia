-- Prove2me | solution 1 for ArtShortage.CashSubsidy.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:42:19.06655+00:00
-- url     : https://prove2.me/submissions/4bb26246-4aeb-4869-828c-4a393dd59cf9

import Mathlib
import Definitions.Def_ArtShortage_CashSubsidy_Model

set_option autoImplicit false
open ArtShortage.CashSubsidy

theorem AS_key (g a b : ℝ) :
    revNoInt g (1/2 - g/8) (1/2) - revNoInt g a b
      = (a - (1/2 - g/8))^2 + B g a * (b - 1/2)^2 := by
  unfold revNoInt B; ring

theorem solution (g lam : ℝ) (hS : Standing g lam) :
    {x : ℝ × ℝ | IsNoIntOpt g x.1 x.2} = {(1/2 - g/8, 1/2)} ∧
      p1 (1/2 - g/8) = 1/2 + g/8 ∧
      p2NoInt g (1/2 - g/8) (1/2) = 1/2 + g/4 + g^2/16 := by
  obtain ⟨hg0, hg4, -⟩ := hS
  have hmem : (1/2 - g/8 : ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hhalf : (1/2 : ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hopt : IsNoIntOpt g (1/2 - g/8) (1/2) := by
    refine ⟨hmem, hhalf, ?_⟩
    intro q1 hq1 q2 _
    have h := AS_key g q1 q2
    have hB : 0 < B g q1 := by unfold B; nlinarith [hq1.2]
    nlinarith [sq_nonneg (q1 - (1/2 - g/8)), mul_nonneg hB.le (sq_nonneg (q2 - 1/2))]
  refine ⟨?_, ?_, ?_⟩
  · ext ⟨a, b⟩
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨ha, hb, hmax⟩
      have h1 := hmax _ hmem _ hhalf
      have h := AS_key g a b
      have hB : 0 < B g a := by unfold B; nlinarith [ha.2]
      have e1 : (a - (1/2 - g/8))^2 = 0 := by
        nlinarith [sq_nonneg (a - (1/2 - g/8)), mul_nonneg hB.le (sq_nonneg (b - 1/2))]
      have e2 : B g a * (b - 1/2)^2 = 0 := by
        nlinarith [sq_nonneg (a - (1/2 - g/8)), mul_nonneg hB.le (sq_nonneg (b - 1/2))]
      have e2' : (b - 1/2)^2 = 0 := by
        rcases mul_eq_zero.mp e2 with h | h
        · exact absurd h hB.ne'
        · exact h
      constructor
      · have := pow_eq_zero_iff (two_ne_zero) |>.mp e1; linarith
      · have := pow_eq_zero_iff (two_ne_zero) |>.mp e2'; linarith
    · rintro ⟨rfl, rfl⟩
      exact hopt
  · unfold p1; ring
  · unfold p2NoInt B; ring
