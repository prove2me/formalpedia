-- Prove2me | solution 1 for AccelVI.LowerBound.bellman_contraction
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-17T17:01:35.448507+00:00
-- url     : https://prove2.me/submissions/eb9e95f9-aa00-43c5-bc09-f83d182e24bc

import Definitions.Def_AccelVI_LowerBound_Setting

open AccelVI.LowerBound

private lemma one_side {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] (M : MDP S A) (hM : M.Valid) (v w : S → ℝ) (s : S) :
    bellman M v s ≤ bellman M w s + M.lam * ‖v - w‖ := by
  classical
  unfold bellman FoundationsML.ReinforcementLearning.BellmanOperator
  apply (Finset.sup'_le_iff _ _).2
  intro a ha
  have hs : ∑ j, M.P s a j * v j ≤ ∑ j, M.P s a j * w j + ‖v - w‖ := by
    calc
      _ ≤ ∑ j, (M.P s a j * w j + M.P s a j * ‖v - w‖) := by
        apply Finset.sum_le_sum
        intro j hj
        have hb : v j - w j ≤ ‖v - w‖ :=
          (le_abs_self (v j - w j)).trans (norm_le_pi_norm (v - w) j)
        nlinarith [(hM.1 s a).1 j]
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, (hM.1 s a).2]
        ring
  have ha' := Finset.le_sup' (fun a => M.r s a + M.lam * ∑ j, M.P s a j * w j) ha
  nlinarith [mul_le_mul_of_nonneg_left hs (le_of_lt hM.2.1)]

theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] (M : MDP S A) (hM : M.Valid) (v w : S → ℝ) :
    ‖bellman M v - bellman M w‖ ≤ M.lam * ‖v - w‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (le_of_lt hM.2.1) (norm_nonneg _))).2
  intro s
  change |bellman M v s - bellman M w s| ≤ _
  have h1 := one_side M hM v w s
  have h2 := one_side M hM w v s
  rw [norm_sub_rev w v] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩
