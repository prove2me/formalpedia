-- Prove2me | solution 1 for AccelVI.LowerBound.eq_3_6
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-17T17:01:39.067074+00:00
-- url     : https://prove2.me/submissions/c9bcff34-d203-46ae-b34c-16ec0200dcd5

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

private lemma chain_zero (n : ℕ) (lam : ℝ) (v : Fin n → ℝ)
    (i : Fin n) (hi : (i : ℕ) = 0) :
    bellman (chainMDP n lam) v i = 1 + lam * v i := by
  classical
  have he : ∀ j : Fin n, ((j : ℕ) = 0 ↔ j = i) := by
    intro j
    constructor
    · intro h; apply Fin.ext; omega
    · rintro rfl; exact hi
  simp [bellman, FoundationsML.ReinforcementLearning.BellmanOperator, chainMDP,
    Finset.univ_unique, hi, he]

private lemma chain_pos (n : ℕ) (lam : ℝ) (v : Fin n → ℝ)
    (i j : Fin n) (hij : (j : ℕ) + 1 = (i : ℕ)) :
    bellman (chainMDP n lam) v i = lam * v j := by
  classical
  have hi : (i : ℕ) ≠ 0 := by omega
  have he : ∀ k : Fin n, ((k : ℕ) + 1 = (i : ℕ) ↔ k = j) := by
    intro k
    constructor
    · intro h; apply Fin.ext; omega
    · rintro rfl; exact hij
  simp [bellman, FoundationsML.ReinforcementLearning.BellmanOperator, chainMDP,
    Finset.univ_unique, hi, he]

private lemma chain_valid (n : ℕ) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    (chainMDP n lam).Valid := by
  refine ⟨?_, h0, h1⟩
  intro i a
  constructor
  · intro j; simp only [chainMDP]; split_ifs <;> norm_num
  · by_cases hi : (i : ℕ) = 0
    · have he : ∀ j : Fin n, ((j : ℕ) = 0 ↔ j = i) := by
        intro j; constructor
        · intro h; apply Fin.ext; omega
        · rintro rfl; exact hi
      simp [chainMDP, hi, he]
    · let j : Fin n := ⟨i.val - 1, by omega⟩
      have he : ∀ k : Fin n, ((k : ℕ) + 1 = (i : ℕ) ↔ k = j) := by
        intro k; constructor
        · intro h; apply Fin.ext; dsimp [j]; omega
        · rintro rfl; dsimp [j]; omega
      simp [chainMDP, hi, he]

private lemma chain_value (n : ℕ) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    bellman (chainMDP n lam) (fun k : Fin n => lam ^ (k : ℕ) / (1-lam)) =
      (fun k : Fin n => lam ^ (k : ℕ) / (1-lam)) := by
  funext i
  by_cases hi : (i : ℕ) = 0
  · rw [chain_zero n lam _ i hi]
    simp only [hi, pow_zero]
    field_simp [ne_of_gt (sub_pos.mpr h1)] <;> ring
  · let j : Fin n := ⟨i.val - 1, by omega⟩
    have hij : (j : ℕ) + 1 = (i : ℕ) := by dsimp [j]; omega
    rw [chain_pos n lam _ i j hij, ← hij, pow_succ]
    ring



private lemma norm_lower {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] (M : MDP S A) (hM : M.Valid) (v w : S → ℝ) :
    (1 - M.lam) * ‖v - w‖ ≤ ‖(v - bellman M v) - (w - bellman M w)‖ := by
  have hc := contract M hM v w
  have ht : ‖v - w‖ ≤ ‖(v - bellman M v) - (w - bellman M w)‖ +
      ‖bellman M v - bellman M w‖ := by
    convert norm_add_le ((v - bellman M v) - (w - bellman M w))
      (bellman M v - bellman M w) using 1 <;> congr 1 <;> abel
  linarith

private lemma norm_upper {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] (M : MDP S A) (hM : M.Valid) (v w : S → ℝ) :
    ‖(v - bellman M v) - (w - bellman M w)‖ ≤ (1 + M.lam) * ‖v - w‖ := by
  have hc := contract M hM v w
  have ht : ‖(v - bellman M v) - (w - bellman M w)‖ ≤ ‖v - w‖ +
      ‖bellman M v - bellman M w‖ := by
    convert norm_sub_le (v - w) (bellman M v - bellman M w) using 1 <;> congr 1 <;> abel
  linarith

private lemma value_unique (n : ℕ) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1)
    (u : Fin n → ℝ) (hu : bellman (chainMDP n lam) u = u) :
    u = (fun k : Fin n => lam ^ (k : ℕ) / (1 - lam)) := by
  have hc := contract (chainMDP n lam) (chain_valid n lam h0 h1) u
    (fun k : Fin n => lam ^ (k : ℕ) / (1 - lam))
  rw [hu, chain_value n lam h0 h1] at hc
  change ‖u - _‖ ≤ lam * ‖u - _‖ at hc
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hn := norm_nonneg (u - (fun k : Fin n => lam ^ (k : ℕ) / (1 - lam)))
  nlinarith

private lemma support (n : ℕ) (lam : ℝ) (v : ℕ → Fin n → ℝ)
    (hv : IsFirstOrder (bellman (chainMDP n lam)) v) (s : ℕ)
    (k : Fin n) (hk : s ≤ (k : ℕ)) : v s k = 0 := by
  induction s using Nat.strong_induction_on generalizing k with
  | h s ih =>
    cases s with
    | zero => rw [hv.1]; rfl
    | succ s =>
      let j : Fin n := ⟨k.val - 1, by omega⟩
      have hjk : (j : ℕ) + 1 = (k : ℕ) := by dsimp [j]; omega
      refine Submodule.span_induction (p := fun x _ => x k = 0) ?_ rfl ?_ ?_ (hv.2 s)
      · intro x hx
        rcases hx with ⟨t, rfl⟩ | ⟨t, rfl⟩
        · exact ih t t.isLt k (by omega)
        · change bellman (chainMDP n lam) (v t) k = 0
          rw [chain_pos n lam (v t) k j hjk, ih t t.isLt j (by dsimp [j]; omega), mul_zero]
      · intro x y hx hy ex ey
        simp [Pi.add_apply, ex, ey]
      · intro a x hx ex
        simp [Pi.smul_apply, ex]

private lemma chain_residual (n : ℕ) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1)
    (v : ℕ → Fin n → ℝ) (hv : IsFirstOrder (bellman (chainMDP n lam)) v)
    (s : ℕ) (hs1 : 1 ≤ s) (hs2 : s ≤ n - 1) :
    lam ^ s ≤ ‖v s - bellman (chainMDP n lam) (v s)‖ := by
  let k : Fin n := ⟨s, by omega⟩
  let u : Fin n → ℝ := fun j => lam ^ (j : ℕ) / (1 - lam)
  have hu : bellman (chainMDP n lam) u = u := chain_value n lam h0 h1
  have hc := norm_le_pi_norm (v s - u) k
  have hk : v s k = 0 := support n lam v hv s k (le_refl s)
  have hp : 0 < 1 - lam := sub_pos.mpr h1
  have hn : 0 ≤ lam ^ s / (1 - lam) := div_nonneg (pow_nonneg h0.le s) hp.le
  simp only [Pi.sub_apply, hk, u, k, zero_sub, norm_neg, Real.norm_eq_abs, abs_of_nonneg hn] at hc
  have hl := norm_lower (chainMDP n lam) (chain_valid n lam h0 h1) (v s) u
  rw [hu, sub_self, sub_zero] at hl
  change (1 - lam) * ‖v s - u‖ ≤ _ at hl
  have hm := mul_le_mul_of_nonneg_left hc hp.le
  have he : (1 - lam) * (lam ^ s / (1 - lam)) = lam ^ s := by field_simp
  rw [he] at hm
  exact hm.trans hl


theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]
    (M : MDP S A) (hM : M.Valid) (v w : S → ℝ) :
    ‖(v - bellman M v) - (w - bellman M w)‖ ≤ (1 + M.lam) * ‖v - w‖ := by
  exact norm_upper M hM v w
