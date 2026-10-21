-- Prove2me | solution 1 for ArtShortage.CashSubsidy.remark_artificial_shortage
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:42:57.197964+00:00
-- url     : https://prove2.me/submissions/3a84e6d4-c71d-4a72-8c35-b5dd86609aa6

import Mathlib
import Definitions.Def_ArtShortage_CashSubsidy_Model

set_option autoImplicit false
open ArtShortage.CashSubsidy

theorem AS_key (g a b : ℝ) :
    revNoInt g (1/2 - g/8) (1/2) - revNoInt g a b
      = (a - (1/2 - g/8))^2 + B g a * (b - 1/2)^2 := by
  unfold revNoInt B; ring

theorem solution (g lam : ℝ) (hS : Standing g lam) :
    (∃ q1 q2, IsNoIntOpt g q1 q2) ∧
      ∀ q1 q2, IsNoIntOpt g q1 q2 → IsArtificialShortage q1 (p1 q1) q2 (p2NoInt g q1 q2) := by
  obtain ⟨hg0, hg4, -⟩ := hS
  have hmem : (1/2 - g/8 : ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hhalf : (1/2 : ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨⟨1/2 - g/8, 1/2, hmem, hhalf, ?_⟩, ?_⟩
  · intro q1 hq1 q2 _
    have h := AS_key g q1 q2
    have hB : 0 < B g q1 := by unfold B; nlinarith [hq1.2]
    nlinarith [sq_nonneg (q1 - (1/2 - g/8)), mul_nonneg hB.le (sq_nonneg (q2 - 1/2))]
  · rintro a b ⟨ha, hb, hmax⟩
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
    have ha' : a = 1/2 - g/8 := by
      have := pow_eq_zero_iff (two_ne_zero) |>.mp e1; linarith
    have hb' : b = 1/2 := by
      have := pow_eq_zero_iff (two_ne_zero) |>.mp e2'; linarith
    subst ha' hb'
    unfold IsArtificialShortage p1 p2NoInt B
    constructor <;> nlinarith [sq_nonneg g]
