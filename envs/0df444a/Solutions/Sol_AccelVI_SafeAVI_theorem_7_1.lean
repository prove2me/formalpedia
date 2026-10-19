-- Prove2me | solution 1 for AccelVI.SafeAVI.theorem_7_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-17T16:58:54.666923+00:00
-- url     : https://prove2.me/submissions/af0f3bb8-abbc-4ec7-a787-282f164e71c6

import Definitions.Def_AccelVI_SafeAVI_Setting

open AccelVI.SafeAVI

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

private lemma contract {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] (M : MDP S A) (hM : M.Valid) (v w : S → ℝ) :
    ‖bellman M v - bellman M w‖ ≤ M.lam * ‖v - w‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (le_of_lt hM.2.1) (norm_nonneg _))).2
  intro s
  change |bellman M v s - bellman M w s| ≤ _
  have h1 := one_side M hM v w s
  have h2 := one_side M hM w v s
  rw [norm_sub_rev w v] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma error_bound {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] (M : MDP S A) (hM : M.Valid) (vstar : S → ℝ)
    (hfix : bellman M vstar = vstar) (v : S → ℝ) :
    ‖v - vstar‖ ≤ (1 - M.lam)⁻¹ * ‖v - bellman M v‖ := by
  have hc := contract M hM v vstar
  rw [hfix] at hc
  have ht : ‖v - vstar‖ ≤ ‖v - bellman M v‖ + ‖bellman M v - vstar‖ := by
    convert norm_add_le (v - bellman M v) (bellman M v - vstar) using 1 <;> congr 1 <;> abel
  have hp : 0 < 1 - M.lam := by linarith [hM.2.2]
  have hb : (1 - M.lam) * ‖v - vstar‖ ≤ ‖v - bellman M v‖ := by linarith
  calc
    _ = (1 - M.lam)⁻¹ * ((1 - M.lam) * ‖v - vstar‖) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hp.le)

private lemma first_step {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] (M : MDP S A) (hM : M.Valid) (lam' α γ : ℝ)
    (hlam' : M.lam ≤ lam') (v0 : S → ℝ) :
    ‖savi M lam' α γ v0 1 - bellman M (savi M lam' α γ v0 1)‖ ≤
      M.lam * ‖v0 - bellman M v0‖ ∧
    M.lam * ‖v0 - bellman M v0‖ ≤ lam' * ‖v0 - bellman M v0‖ := by
  exact ⟨contract M hM v0 (bellman M v0), mul_le_mul_of_nonneg_right hlam' (norm_nonneg _)⟩

private lemma residual_bound {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] (M : MDP S A) (hM : M.Valid) (lam' α γ : ℝ)
    (hlam' : M.lam ≤ lam') (v0 : S → ℝ) (s : ℕ) :
    ‖savi M lam' α γ v0 s - bellman M (savi M lam' α γ v0 s)‖ ≤
      lam' ^ s * ‖v0 - bellman M v0‖ := by
  have hp : 0 ≤ lam' := (le_of_lt hM.2.1).trans hlam'
  induction s using Nat.twoStepInduction with
  | zero => simp [savi]
  | one => simpa using (first_step M hM lam' α γ hlam' v0).1.trans (first_step M hM lam' α γ hlam' v0).2
  | more s ih ih1 =>
    rw [savi]
    split_ifs with h
    · exact h
    · calc
        _ ≤ M.lam * ‖savi M lam' α γ v0 (s + 1) -
          bellman M (savi M lam' α γ v0 (s + 1))‖ :=
            contract M hM _ _
        _ ≤ lam' * (lam' ^ (s + 1) * ‖v0 - bellman M v0‖) :=
          mul_le_mul hlam' ih1 (norm_nonneg _) hp
        _ = _ := by rw [pow_succ]; ring

open Filter in
 theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] (M : MDP S A) (hM : M.Valid) (lam' α γ : ℝ)
    (hlam' : M.lam ≤ lam') (hlam'1 : lam' < 1) (hα : 0 < α) (hγ : 0 < γ)
    (v0 vstar : S → ℝ) (hfix : bellman M vstar = vstar) :
    Filter.Tendsto (savi M lam' α γ v0) Filter.atTop (nhds vstar) ∧
      ∃ C : ℝ, ∀ s : ℕ, ‖savi M lam' α γ v0 s - vstar‖ ≤ C * lam' ^ s := by
  let C := (1 - M.lam)⁻¹ * ‖v0 - bellman M v0‖
  have hp : 0 < 1 - M.lam := by linarith [hM.2.2]
  have hb : ∀ s : ℕ, ‖savi M lam' α γ v0 s - vstar‖ ≤ C * lam' ^ s := by
    intro s
    calc
      _ ≤ (1 - M.lam)⁻¹ * ‖savi M lam' α γ v0 s - bellman M (savi M lam' α γ v0 s)‖ :=
        error_bound M hM vstar hfix _
      _ ≤ (1 - M.lam)⁻¹ * (lam' ^ s * ‖v0 - bellman M v0‖) :=
        mul_le_mul_of_nonneg_left (residual_bound M hM lam' α γ hlam' v0 s) (inv_nonneg.mpr hp.le)
      _ = _ := by dsimp [C]; ring
  refine ⟨?_, C, hb⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun s => norm_nonneg _) hb
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ((le_of_lt hM.2.1).trans hlam') hlam'1).const_mul C