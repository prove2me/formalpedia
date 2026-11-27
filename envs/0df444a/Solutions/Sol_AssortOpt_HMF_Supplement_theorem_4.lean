-- Prove2me | solution 1 for AssortOpt.HMF.Supplement.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:37:21.424485+00:00
-- url     : https://prove2.me/submissions/59995eda-5fe8-4431-ba81-9ee8d8a25ca6

import Mathlib
import Definitions.Def_AssortOpt_HMF_Supplement_TopTwoFamily

open AssortOpt
open AssortOpt.HMF
open AssortOpt.HMF.Supplement

theorem solution :
    ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M →
      (∀ (n : ℕ) (D : ListDist n), IsThm4Instance M D →
          (n : ℝ) / 2 ≤ revMech D (thm4Price M) topTwoLottery) ∧
      (∃ (C : ℝ) (N : ℕ), ∀ n : ℕ, N ≤ n → ∀ D : ListDist n, IsThm4Instance M D →
          ∀ S : Finset (Fin n),
            revAssort D (thm4Price M) S ≤ (n : ℝ) / Real.exp 1 + C * Real.log n) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ D : ListDist n, IsThm4Instance M D →
          ∀ S : Finset (Fin n),
            revAssort D (thm4Price M) S ≤
              (2 / Real.exp 1 + ε) * revMech D (thm4Price M) topTwoLottery) := by
                classical
                open Finset in
                have hlogle : ∀ y : ℝ, 0 < y → Real.log y ≤ y / Real.exp 1 := by
                  intro y hy
                  have h1 := Real.log_le_sub_one_of_pos (div_pos hy (Real.exp_pos 1))
                  rw [Real.log_div hy.ne' (Real.exp_pos 1).ne', Real.log_exp] at h1
                  linarith
                have hstep : ∀ y : ℝ, 0 < y → 1 / (y + 1) ≤ Real.log (y + 1) - Real.log y := by
                  intro y hy
                  have hy1 : (0:ℝ) < y + 1 := by linarith
                  have h1 := Real.log_le_sub_one_of_pos (div_pos hy hy1)
                  rw [Real.log_div hy.ne' hy1.ne'] at h1
                  have : y / (y + 1) - 1 = - (1 / (y + 1)) := by field_simp; ring
                  linarith
                have hharm : ∀ x : ℝ, 1 ≤ x → ∀ k : ℕ,
                    ∑ i ∈ Finset.range k, 1 / (x + i) ≤ 1 / x + Real.log (x + k) - Real.log x := by
                  intro x hx k
                  have aux : ∀ k : ℕ, ∑ i ∈ Finset.range (k + 1), 1 / (x + i)
                      ≤ 1 / x + Real.log (x + k) - Real.log x := by
                    intro k
                    induction k with
                    | zero => simp
                    | succ k ih =>
                      rw [Finset.sum_range_succ]
                      have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
                      have := hstep (x + k) (by linarith)
                      push_cast
                      have e : x + ((k:ℝ) + 1) = x + k + 1 := by ring
                      rw [e]
                      linarith
                  cases k with
                  | zero =>
                    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, add_zero]
                    have : 0 < 1 / x := one_div_pos.mpr (by linarith)
                    linarith
                  | succ k =>
                    have h1 := aux k
                    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
                    have h2 : Real.log (x + k) ≤ Real.log (x + ((k+1 : ℕ) : ℝ)) :=
                      Real.log_le_log (by linarith) (by push_cast; linarith)
                    linarith
                have hgeo : ∀ M : ℝ, 2 ≤ M → ∀ b : ℕ, ∑ a ∈ Finset.range b, M ^ (a + 1) ≤ M ^ (b + 1) := by
                  intro M hM b
                  induction b with
                  | zero => simp; linarith
                  | succ b ih =>
                    rw [Finset.sum_range_succ]
                    have : M ^ (b + 1 + 1) = M * M ^ (b+1) := by ring
                    have hp : 0 ≤ M ^ (b+1) := pow_nonneg (by linarith) _
                    nlinarith
                have hcardlt : ∀ (n : ℕ) (b : Fin n),
                    (Finset.univ.filter (fun a : Fin n => a < b)).card = b.val := by
                  intro n b; rw [← Fin.card_Iio b]; congr 1; ext a; simp
                have hrange : ∀ (M : ℝ) (n : ℕ) (b : Fin n),
                    ∑ a : Fin n, (if a < b then M ^ (a.val + 1) else 0) = ∑ a ∈ Finset.range b.val, M ^ (a + 1) := by
                  intro M n b
                  calc ∑ a : Fin n, (if a < b then M ^ (a.val + 1) else 0)
                      = ∑ a : Fin n, (fun i : ℕ => if i < b.val then M ^ (i + 1) else 0) a.val := by
                        apply Finset.sum_congr rfl; intro a _
                        by_cases h : a < b
                        · have h' : a.val < b.val := h
                          simp [h, h']
                        · have h' : ¬ a.val < b.val := h
                          simp [h, h']
                    _ = ∑ i ∈ Finset.range n, (fun i : ℕ => if i < b.val then M ^ (i + 1) else 0) i :=
                        Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < b.val then M ^ (i + 1) else (0:ℝ)) n
                    _ = ∑ i ∈ Finset.range b.val, M ^ (i + 1) := by
                        rw [← Finset.sum_filter]; congr 1; ext i
                        simp only [Finset.mem_filter, Finset.mem_range]
                        have := b.isLt
                        constructor
                        · intro h; exact h.2
                        · intro h; exact ⟨by omega, h⟩
                have hmid : ∀ (n : ℕ) (S : Finset (Fin n)),
                    ∑ b ∈ S, ((Finset.univ.filter (fun a : Fin n => a < b ∧ a ∉ S)).card : ℝ) / (b.val : ℝ)
                      ≤ 1 + n / Real.exp 1 := by
                  intro n S
                  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = S.card := ⟨_, rfl⟩
                  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = n - k := ⟨_, rfl⟩
                  have hkn : k ≤ n := by rw [hk]; simpa using S.card_le_univ
                  obtain ⟨s, hs⟩ : ∃ s : Fin n → ℕ, s = fun b => (S.filter (fun a => a < b)).card := ⟨_, rfl⟩
                  have h1 : ∀ b ∈ S, ((Finset.univ.filter (fun a : Fin n => a < b ∧ a ∉ S)).card : ℝ) / (b.val : ℝ)
                      ≤ (m : ℝ) / (m + s b) := by
                    intro b hb
                    obtain ⟨g, hg⟩ : ∃ g : ℕ, g = (Finset.univ.filter (fun a : Fin n => a < b ∧ a ∉ S)).card :=
                      ⟨_, rfl⟩
                    rw [← hg]
                    have hgm : g ≤ m := by
                      have hsub : Finset.univ.filter (fun a : Fin n => a < b ∧ a ∉ S) ⊆ Sᶜ := by
                        intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
                        simp [ha.2]
                      have := Finset.card_le_card hsub
                      rw [Finset.card_compl, Fintype.card_fin] at this
                      omega
                    have hgs : (S.filter (fun a => a < b)).card + g = b.val := by
                      rw [← hcardlt n b, hg,
                        ← Finset.card_filter_add_card_filter_not
                          (s := Finset.univ.filter (fun a : Fin n => a < b)) (fun a => a ∈ S)]
                      congr 1
                      · congr 1; ext a; simp [and_comm]
                      · congr 1; ext a; simp
                    have hsb : s b = (S.filter (fun a => a < b)).card := by rw [hs]
                    rw [← hsb] at hgs
                    rcases Nat.eq_zero_or_pos g with h0 | hgpos
                    · rw [h0]; simp only [Nat.cast_zero, zero_div]; positivity
                    · have hbv : (b.val : ℝ) = (g : ℝ) + s b := by
                        rw [← hgs]; push_cast; ring
                      rw [hbv]
                      have hg0 : (0:ℝ) < g := by exact_mod_cast hgpos
                      have hgm' : (g:ℝ) ≤ m := by exact_mod_cast hgm
                      have hs0 : (0:ℝ) ≤ s b := Nat.cast_nonneg _
                      rw [div_le_div_iff₀ (by linarith) (by linarith)]
                      nlinarith
                  have h2 : ∑ b ∈ S, (m:ℝ) / (m + s b) ≤ ∑ i ∈ Finset.range k, (m:ℝ) / (m + i) := by
                    have hlt : ∀ b ∈ S, ∀ b' ∈ S, b < b' → s b < s b' := by
                      intro b hb b' hb' hlt
                      rw [hs]
                      apply Finset.card_lt_card
                      refine ⟨?_, ?_⟩
                      · intro a ha
                        simp only [Finset.mem_filter] at ha ⊢
                        exact ⟨ha.1, lt_trans ha.2 hlt⟩
                      · intro hsub
                        have := hsub (Finset.mem_filter.mpr ⟨hb, hlt⟩)
                        simp at this
                    have hinj : Set.InjOn s S := by
                      intro b hb b' hb' hbb
                      by_contra hne
                      rcases lt_or_gt_of_ne hne with h | h
                      · have := hlt b hb b' hb' h; omega
                      · have := hlt b' hb' b hb h; omega
                    rw [← Finset.sum_image (f := fun i : ℕ => (m:ℝ) / (m + i)) hinj]
                    apply Finset.sum_le_sum_of_subset_of_nonneg
                    · intro i hi
                      rw [Finset.mem_image] at hi
                      obtain ⟨b, hb, rfl⟩ := hi
                      rw [Finset.mem_range, hk, hs]
                      apply Finset.card_lt_card
                      refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
                      have := h hb
                      simp at this
                    · intro i _ _; positivity
                  have h3 : ∑ i ∈ Finset.range k, (m:ℝ) / (m + i) ≤ 1 + n / Real.exp 1 := by
                    rcases Nat.eq_zero_or_pos m with h0 | hpos
                    · simp only [h0, Nat.cast_zero, zero_div, Finset.sum_const_zero]; positivity
                    · have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hpos
                      have hm0 : (0:ℝ) < m := by linarith
                      have hH := hharm m hm1 k
                      have e : ∑ i ∈ Finset.range k, (m:ℝ) / (m + i) = m * ∑ i ∈ Finset.range k, 1 / ((m:ℝ) + i) := by
                        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
                      rw [e]
                      have hmk : (m:ℝ) + k = n := by exact_mod_cast (show m + k = n by omega)
                      rw [hmk] at hH
                      have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
                      have hn : (0:ℝ) < n := by linarith
                      have hl : Real.log n - Real.log m = Real.log ((n:ℝ)/m) := (Real.log_div hn.ne' hm0.ne').symm
                      have hlog := hlogle ((n:ℝ)/m) (div_pos hn hm0)
                      have hmm : (m:ℝ) * (1/m) = 1 := by field_simp
                      calc (m:ℝ) * ∑ i ∈ Finset.range k, 1 / ((m:ℝ) + i)
                          ≤ m * (1/m + Real.log n - Real.log m) := mul_le_mul_of_nonneg_left hH hm0.le
                        _ = 1 + m * Real.log ((n:ℝ)/m) := by rw [← hl]; linear_combination hmm
                        _ ≤ 1 + m * ((n/m)/Real.exp 1) := by gcongr
                        _ = 1 + n / Real.exp 1 := by field_simp
                  calc _ ≤ ∑ b ∈ S, (m:ℝ) / (m + s b) := Finset.sum_le_sum h1
                    _ ≤ _ := h2
                    _ ≤ _ := h3
                have key : ∀ M : ℝ, 2 ≤ M → ∀ (n : ℕ) (D : ListDist n), IsThm4Instance M D →
                    (n : ℝ) / 2 ≤ revMech D (thm4Price M) topTwoLottery ∧
                    ∀ S : Finset (Fin n), revAssort D (thm4Price M) S ≤
                      1 + n / Real.exp 1 + 3 * (1 + Real.log (1 + n)) := by
                  intro M hM n D hD
                  have hM0 : 0 < M := by linarith
                  have hpow : ∀ k : ℕ, 0 < M ^ k := fun k => pow_pos hM0 k
                  obtain ⟨T, hT⟩ : ∃ T : Finset (List (Fin n)), T = insert []
                      ((Finset.univ.image fun i : Fin n => [i]) ∪
                        (Finset.univ.image fun p : Fin n × Fin n => [p.1, p.2])) := ⟨_, rfl⟩
                  have hnn : ∀ ℓ : List (Fin n), ℓ ≠ [] → 0 ≤ thm4Prob M ℓ := by
                    intro ℓ hℓ
                    rcases ℓ with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
                    · exact absurd rfl hℓ
                    · simp only [thm4Prob]; split_ifs
                      · exact inv_nonneg.mpr hM0.le
                      · exact le_refl 0
                    · simp only [thm4Prob]; split_ifs
                      · exact div_nonneg (inv_nonneg.mpr (hpow _).le) (Nat.cast_nonneg _)
                      · exact le_refl 0
                    · simp [thm4Prob]
                  have hsub : D.supp ⊆ T := by
                    intro ℓ hℓ
                    have hp : 0 < thm4Prob M ℓ := by rw [← hD.1 ℓ hℓ]; exact D.pos ℓ hℓ
                    rcases ℓ with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
                    · simp [hT]
                    · simp [hT]
                    · simp [hT]
                    · simp [thm4Prob] at hp
                  have hsum : ∀ G : List (Fin n) → ℝ, G [] = 0 →
                      ∑ ℓ ∈ D.supp, D.p ℓ * G ℓ =
                        ∑ b : Fin n, (thm4Prob M [b] * G [b] + ∑ a : Fin n, thm4Prob M [a, b] * G [a, b]) := by
                    intro G hG0
                    have h1 : ∑ ℓ ∈ D.supp, D.p ℓ * G ℓ = ∑ ℓ ∈ D.supp, thm4Prob M ℓ * G ℓ :=
                      Finset.sum_congr rfl (fun ℓ hℓ => by rw [hD.1 ℓ hℓ])
                    have h2 : ∑ ℓ ∈ D.supp, thm4Prob M ℓ * G ℓ = ∑ ℓ ∈ T, thm4Prob M ℓ * G ℓ := by
                      apply Finset.sum_subset hsub
                      intro ℓ _ hns
                      by_cases he : ℓ = []
                      · rw [he, hG0, mul_zero]
                      · have hn1 : ¬ 0 < thm4Prob M ℓ := fun h => hns (hD.2 ℓ h)
                        have hn2 := hnn ℓ he
                        have : thm4Prob M ℓ = 0 := by linarith
                        rw [this, zero_mul]
                    have hinj1 : Set.InjOn (fun i : Fin n => [i]) (Finset.univ : Finset (Fin n)) := by
                      intro i _ j _ h; simpa using h
                    have hinj2 : Set.InjOn (fun p : Fin n × Fin n => [p.1, p.2])
                        (Finset.univ : Finset (Fin n × Fin n)) := by
                      intro p _ q _ h
                      simp only [List.cons.injEq, and_true] at h
                      exact Prod.ext h.1 h.2
                    have hdisj : Disjoint (Finset.univ.image fun i : Fin n => [i])
                        (Finset.univ.image fun p : Fin n × Fin n => [p.1, p.2]) := by
                      rw [Finset.disjoint_left]
                      intro ℓ h1 h2
                      simp only [Finset.mem_image, Finset.mem_univ, true_and] at h1 h2
                      obtain ⟨i, rfl⟩ := h1
                      obtain ⟨p, hp⟩ := h2
                      simp at hp
                    have h3 : ∑ ℓ ∈ T, thm4Prob M ℓ * G ℓ =
                        ∑ i : Fin n, thm4Prob M [i] * G [i] +
                          ∑ b : Fin n, ∑ a : Fin n, thm4Prob M [a, b] * G [a, b] := by
                      rw [hT, Finset.sum_insert (by simp), hG0, mul_zero, zero_add,
                        Finset.sum_union hdisj, Finset.sum_image hinj1, Finset.sum_image hinj2,
                        Fintype.sum_prod_type, Finset.sum_comm]
                    rw [h1, h2, h3, Finset.sum_add_distrib]
                  refine ⟨?_, ?_⟩
                  · -- the mechanism
                    have hGm1 : ∀ c : Fin n, ∑ j ∈ [c].toFinset, thm4Price M j * topTwoLottery [c] j
                        = M ^ (c.val + 1) / 2 := by
                      intro c
                      have hmin : min (2⁻¹ : ℝ) 1 = 2⁻¹ := min_eq_left (by norm_num)
                      simp [topTwoLottery, budgetMech, incrementMech, budgetFn, thm4Price, hmin]
                      ring
                    have hGm2 : ∀ a c : Fin n, a ≠ c →
                        ∑ j ∈ [a, c].toFinset, thm4Price M j * topTwoLottery [a, c] j
                          = M ^ (a.val + 1) / 2 + M ^ (c.val + 1) / 2 := by
                      intro a c hac
                      rw [List.toFinset_cons, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
                        Finset.sum_pair hac]
                      have hca : c ≠ a := fun h => hac h.symm
                      have hmin : min (2⁻¹ : ℝ) 1 = 2⁻¹ := min_eq_left (by norm_num)
                      simp [topTwoLottery, budgetMech, incrementMech, budgetFn, thm4Price, hac, hca,
                        List.idxOf_cons_ne, Finset.card_pair hac, hmin]
                      ring
                    have e := hsum (fun ℓ => ∑ j ∈ ℓ.toFinset, thm4Price M j * topTwoLottery ℓ j) (by simp)
                    unfold revMech
                    rw [e]
                    have hn2 : (n:ℝ) / 2 = ∑ b : Fin n, (1/2 : ℝ) := by simp; ring
                    rw [hn2]
                    apply Finset.sum_le_sum
                    intro b _
                    have hpair : ∀ a : Fin n, (if a < b then (1:ℝ) / (2 * b.val) else 0) ≤
                        thm4Prob M [a, b] * ∑ j ∈ [a, b].toFinset, thm4Price M j * topTwoLottery [a, b] j := by
                      intro a
                      by_cases hab : a < b
                      · rw [if_pos hab, hGm2 a b (ne_of_lt hab)]
                        simp only [thm4Prob, if_pos hab]
                        have hab' : a.val < b.val := hab
                        have hbpos : (0:ℝ) < (b.val : ℝ) := by exact_mod_cast (by omega : 0 < b.val)
                        have hY := hpow (b.val + 1)
                        have hX := hpow (a.val + 1)
                        have : (M ^ (b.val + 1))⁻¹ / (b.val : ℝ) * (M ^ (a.val + 1) / 2 + M ^ (b.val + 1) / 2)
                            = (M ^ (b.val + 1))⁻¹ / (b.val : ℝ) * (M ^ (a.val + 1) / 2) + 1 / (2 * b.val) := by
                          field_simp
                        rw [this]
                        have : 0 ≤ (M ^ (b.val + 1))⁻¹ / (b.val : ℝ) * (M ^ (a.val + 1) / 2) := by positivity
                        linarith
                      · simp [thm4Prob, hab]
                    by_cases h0 : b.val = 0
                    · have hs : 0 ≤ ∑ a : Fin n, thm4Prob M [a, b] *
                          ∑ j ∈ [a, b].toFinset, thm4Price M j * topTwoLottery [a, b] j := by
                        apply Finset.sum_nonneg; intro a _
                        exact le_trans (by split_ifs <;> positivity) (hpair a)
                      rw [hGm1 b]
                      have hp1 : thm4Prob M [b] = M⁻¹ := by simp [thm4Prob, h0]
                      rw [hp1, h0, zero_add, pow_one]
                      have : M⁻¹ * (M / 2) = 1 / 2 := by field_simp
                      linarith
                    · have hs := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hpair a)
                      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcardlt] at hs
                      have hbpos : (0:ℝ) < (b.val : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero h0)
                      have : (b.val : ℝ) * (1 / (2 * b.val)) = 1 / 2 := by field_simp
                      have hp1 : thm4Prob M [b] = 0 := by simp [thm4Prob, h0]
                      rw [hp1, zero_mul, zero_add]
                      linarith
                  · intro S
                    have hGa : revAssort D (thm4Price M) S = ∑ ℓ ∈ D.supp, D.p ℓ *
                        ∑ j ∈ S, (if Chooses S ℓ j then thm4Price M j else 0) := by
                      unfold revAssort choiceProb
                      simp_rw [Finset.sum_filter, Finset.mul_sum]
                      rw [Finset.sum_comm]
                      apply Finset.sum_congr rfl; intro ℓ _; apply Finset.sum_congr rfl; intro j _
                      split_ifs <;> ring
                    have e := hsum (fun ℓ => ∑ j ∈ S, (if Chooses S ℓ j then thm4Price M j else 0))
                      (by simp [Chooses])
                    rw [hGa, e]
                    have hC1 : ∀ c : Fin n, ∑ j ∈ S, (if Chooses S [c] j then thm4Price M j else 0)
                        = if c ∈ S then M ^ (c.val + 1) else 0 := by
                      intro c
                      by_cases hc : c ∈ S
                      · have hc' : ∀ j, Chooses S [c] j ↔ c = j := by intro j; simp [Chooses, hc]
                        simp only [hc', if_pos hc]
                        rw [Finset.sum_ite_eq S c]; simp [hc, thm4Price]
                      · have hc' : ∀ j, ¬ Chooses S [c] j := by intro j; simp [Chooses, hc]
                        simp [hc', hc]
                    have hC2 : ∀ a c : Fin n, ∑ j ∈ S, (if Chooses S [a, c] j then thm4Price M j else 0)
                        = if a ∈ S then M ^ (a.val + 1) else if c ∈ S then M ^ (c.val + 1) else 0 := by
                      intro a c
                      by_cases ha : a ∈ S
                      · have hc : ∀ j, Chooses S [a, c] j ↔ a = j := by intro j; simp [Chooses, ha]
                        simp only [hc, if_pos ha]
                        rw [Finset.sum_ite_eq S a]; simp [ha, thm4Price]
                      · by_cases hc' : c ∈ S
                        · have hc : ∀ j, Chooses S [a, c] j ↔ c = j := by intro j; simp [Chooses, ha, hc']
                          simp only [hc, if_neg ha, if_pos hc']
                          rw [Finset.sum_ite_eq S c]; simp [hc', thm4Price]
                        · have hc : ∀ j, ¬ Chooses S [a, c] j := by intro j; simp [Chooses, ha, hc']
                          simp [hc, ha, hc']
                    have hterm : ∀ a b : Fin n, thm4Prob M [a, b] *
                        ∑ j ∈ S, (if Chooses S [a, b] j then thm4Price M j else 0) ≤
                        (if b ∈ S then (if a < b ∧ a ∉ S then 1 / (b.val : ℝ) else 0) else 0) +
                          (if a < b then (M ^ (b.val + 1))⁻¹ / (b.val : ℝ) * M ^ (a.val + 1) else 0) := by
                      intro a b
                      rw [hC2]
                      have hI : 0 ≤ (if b ∈ S then (if a < b ∧ a ∉ S then 1 / (b.val : ℝ) else 0) else 0) := by
                        split_ifs <;> positivity
                      by_cases hab : a < b
                      · have hab' : a.val < b.val := hab
                        have hbpos : (0:ℝ) < (b.val : ℝ) := by exact_mod_cast (by omega : 0 < b.val)
                        have hY := hpow (b.val + 1)
                        have hq : 0 ≤ (M ^ (b.val + 1))⁻¹ / (b.val : ℝ) * M ^ (a.val + 1) := by positivity
                        have hp2 : thm4Prob M [a, b] = (M ^ (b.val + 1))⁻¹ / (b.val : ℝ) := by
                          simp [thm4Prob, hab]
                        rw [hp2, if_pos hab]
                        by_cases haS : a ∈ S
                        · rw [if_pos haS]; linarith
                        · by_cases hbS : b ∈ S
                          · rw [if_neg haS, if_pos hbS, if_pos hbS, if_pos (And.intro hab haS)]
                            have : (M ^ (b.val + 1))⁻¹ / (b.val : ℝ) * M ^ (b.val + 1) = 1 / (b.val : ℝ) := by
                              field_simp
                            linarith
                          · rw [if_neg haS, if_neg hbS, mul_zero]; linarith
                      · have hp2 : thm4Prob M [a, b] = 0 := by simp [thm4Prob, hab]
                        rw [hp2, zero_mul, if_neg hab]; linarith
                    have hb : ∀ b : Fin n, thm4Prob M [b] *
                          ∑ j ∈ S, (if Chooses S [b] j then thm4Price M j else 0) +
                        ∑ a : Fin n, thm4Prob M [a, b] *
                          ∑ j ∈ S, (if Chooses S [a, b] j then thm4Price M j else 0) ≤
                        (if b ∈ S then
                            ((Finset.univ.filter (fun a : Fin n => a < b ∧ a ∉ S)).card : ℝ) / (b.val : ℝ)
                          else 0) + 3 * (1 / (1 + (b.val : ℝ))) := by
                      intro b
                      have hb0 : (0:ℝ) ≤ b.val := Nat.cast_nonneg _
                      have hfirst : thm4Prob M [b] * ∑ j ∈ S, (if Chooses S [b] j then thm4Price M j else 0)
                          ≤ 1 / (1 + (b.val : ℝ)) := by
                        rw [hC1]
                        by_cases h0 : b.val = 0
                        · have hp1 : thm4Prob M [b] = M⁻¹ := by simp [thm4Prob, h0]
                          rw [hp1, h0]
                          have : M⁻¹ * M = 1 := by field_simp
                          split_ifs
                          · simp only [zero_add, pow_one, Nat.cast_zero]; rw [this]; norm_num
                          · simp
                        · have hp1 : thm4Prob M [b] = 0 := by simp [thm4Prob, h0]
                          rw [hp1, zero_mul]; positivity
                      have hsec := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hterm a b)
                      rw [Finset.sum_add_distrib] at hsec
                      have hA : ∑ a : Fin n, (if b ∈ S then (if a < b ∧ a ∉ S then 1 / (b.val : ℝ) else 0) else 0)
                          = (if b ∈ S then
                            ((Finset.univ.filter (fun a : Fin n => a < b ∧ a ∉ S)).card : ℝ) / (b.val : ℝ)
                          else 0) := by
                        by_cases hbS : b ∈ S
                        · simp only [if_pos hbS]
                          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; ring
                        · simp [hbS]
                      have hB : ∑ a : Fin n, (if a < b then (M ^ (b.val + 1))⁻¹ / (b.val : ℝ) * M ^ (a.val + 1) else 0)
                          ≤ 2 * (1 / (1 + (b.val : ℝ))) := by
                        have e1 : ∑ a : Fin n, (if a < b then (M ^ (b.val + 1))⁻¹ / (b.val : ℝ) * M ^ (a.val + 1) else 0)
                            = (M ^ (b.val + 1))⁻¹ / (b.val : ℝ) * ∑ a : Fin n, (if a < b then M ^ (a.val + 1) else 0) := by
                          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; split_ifs <;> simp
                        rw [e1, hrange]
                        have hg := hgeo M hM b.val
                        have hY := hpow (b.val + 1)
                        by_cases h0 : b.val = 0
                        · rw [h0]; simp
                        · have hbpos : (1:ℝ) ≤ (b.val : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero h0)
                          calc (M ^ (b.val + 1))⁻¹ / (b.val : ℝ) * ∑ a ∈ Finset.range b.val, M ^ (a + 1)
                              ≤ (M ^ (b.val + 1))⁻¹ / (b.val : ℝ) * M ^ (b.val + 1) :=
                                mul_le_mul_of_nonneg_left hg (by positivity)
                            _ = 1 / (b.val : ℝ) := by field_simp
                            _ ≤ 2 * (1 / (1 + (b.val : ℝ))) := by
                                rw [div_le_iff₀ (by linarith)]
                                field_simp
                                linarith
                      rw [hA] at hsec
                      linarith
                    calc _ ≤ ∑ b : Fin n, ((if b ∈ S then
                            ((Finset.univ.filter (fun a : Fin n => a < b ∧ a ∉ S)).card : ℝ) / (b.val : ℝ)
                          else 0) + 3 * (1 / (1 + (b.val : ℝ)))) := Finset.sum_le_sum (fun b _ => hb b)
                      _ = ∑ b ∈ S, ((Finset.univ.filter (fun a : Fin n => a < b ∧ a ∉ S)).card : ℝ) / (b.val : ℝ)
                            + 3 * ∑ i ∈ Finset.range n, 1 / (1 + (i : ℝ)) := by
                          rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum,
                            Fin.sum_univ_eq_sum_range (fun i : ℕ => 1 / (1 + (i : ℝ))) n]
                      _ ≤ 1 + n / Real.exp 1 + 3 * (1 + Real.log (1 + n)) := by
                          have h1 := hmid n S
                          have h2 := hharm 1 le_rfl n
                          rw [Real.log_one, div_one, sub_zero] at h2
                          linarith
                refine ⟨2, fun M hM => ⟨fun n D hD => (key M hM n D hD).1,
                  ⟨10, 3, fun n hn D hD S => ?_⟩, fun ε hε => ?_⟩⟩
                · have h := (key M hM n D hD).2 S
                  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast hn
                  have hlogn : 1 ≤ Real.log n := by
                    have he : Real.exp 1 ≤ n := by
                      have := Real.exp_one_lt_d9; norm_num at this; linarith
                    have := Real.log_le_log (Real.exp_pos 1) he
                    rwa [Real.log_exp] at this
                  have hlog1n : Real.log (1 + n) ≤ 2 * Real.log n := by
                    have := Real.log_le_log (by linarith) (show (1:ℝ) + n ≤ n * n by nlinarith)
                    rw [Real.log_mul (ne_of_gt (by linarith)) (ne_of_gt (by linarith))] at this
                    linarith
                  linarith
                · obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp
                    (Real.isLittleO_log_id_atTop.bound (show (0:ℝ) < ε / 24 by positivity))
                  refine ⟨max 3 (max ⌈a⌉₊ ⌈16 / ε⌉₊), fun n hn D hD S => ?_⟩
                  have hk := key M hM n D hD
                  have h3 : 3 ≤ n := le_trans (le_max_left _ _) hn
                  have hn1 : ⌈a⌉₊ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
                  have hn2 : ⌈16 / ε⌉₊ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
                  have hna : a ≤ n := le_trans (Nat.le_ceil a) (by exact_mod_cast hn1)
                  have hne : 16 / ε ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hn2)
                  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast h3
                  have hlog := ha n hna
                  simp only [id, Real.norm_eq_abs] at hlog
                  rw [abs_of_pos (by linarith : (0:ℝ) < n)] at hlog
                  have hlog' : Real.log n ≤ ε / 24 * n := le_trans (le_abs_self _) hlog
                  have hlog1n : Real.log (1 + n) ≤ 2 * Real.log n := by
                    have := Real.log_le_log (by linarith) (show (1:ℝ) + n ≤ n * n by nlinarith)
                    rw [Real.log_mul (ne_of_gt (by linarith)) (ne_of_gt (by linarith))] at this
                    linarith
                  have h16 : 16 ≤ ε * n := by
                    rw [div_le_iff₀ hε] at hne; linarith
                  have hpos : 0 ≤ 2 / Real.exp 1 + ε := (add_pos (div_pos two_pos (Real.exp_pos 1)) hε).le
                  have hmul := mul_le_mul_of_nonneg_left hk.1 hpos
                  have heq : (2 / Real.exp 1 + ε) * ((n:ℝ) / 2) = n / Real.exp 1 + ε * n / 2 := by
                    field_simp
                  have := hk.2 S
                  nlinarith
