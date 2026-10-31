-- Prove2me | solution 1 for AdaptSubCover.Rounds.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:04:34.878889+00:00
-- url     : https://prove2.me/submissions/0f956774-b395-4415-9744-b6797d0056d6

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_Analysis

open AdaptSubCover.Rounds

namespace ASCL45

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

theorem go_prefix (stop : History m U → Bool) (ω : Fin m → U) :
    ∀ (L : List (Fin m)) (h : History m U), h <+: Round.go stop ω L h
  | [], h => by simp [Round.go]
  | i :: L, h => by
    simp only [Round.go]
    split_ifs with h1 h2
    · exact List.prefix_refl _
    · exact go_prefix stop ω L h
    · exact (List.prefix_append h _).trans (go_prefix stop ω L _)

theorem go_noStop (stop : History m U → Bool) (ω : Fin m → U) :
    ∀ (L : List (Fin m)) (h : History m U) (j : ℕ), h.length ≤ j →
      j < (Round.go stop ω L h).length → stop ((Round.go stop ω L h).take j) = false
  | [], h, j, hj1, hj2 => by simp [Round.go] at hj2; omega
  | i :: L, h, j, hj1, hj2 => by
    by_cases hs : stop h = true
    · simp [Round.go, hs] at hj2; omega
    · have hs' : stop h = false := by simpa using hs
      by_cases hm : i ∈ h.items
      · have e : Round.go stop ω (i :: L) h = Round.go stop ω L h := by
          simp [Round.go, hs', hm]
        rw [e] at hj2 ⊢
        exact go_noStop stop ω L h j hj1 hj2
      · have e : Round.go stop ω (i :: L) h = Round.go stop ω L (h ++ [(i, ω i)]) := by
          simp [Round.go, hs', hm]
        rw [e] at hj2 ⊢
        rcases Nat.lt_or_ge j (h ++ [(i, ω i)]).length with hj | hj
        · have hjl : j = h.length := by simp at hj; omega
          subst hjl
          obtain ⟨t, ht⟩ := go_prefix stop ω L (h ++ [(i, ω i)])
          rw [← ht]
          simp only [List.append_assoc, List.take_left']
          exact hs'
        · exact go_noStop stop ω L _ j hj hj2

/-- Telescoping harmonic-type bound. -/
theorem tele (a : ℕ → ℝ) :
    ∀ n : ℕ, (∀ j ≤ n, 0 < a j) → (∀ j < n, a (j + 1) ≤ a j) →
      ∑ j ∈ Finset.range n, (a j - a (j + 1)) / a j ≤ Real.log (a 0) - Real.log (a n)
  | 0, _, _ => by simp
  | n + 1, hpos, hmono => by
    rw [Finset.sum_range_succ]
    have ih := tele a n (fun j hj => hpos j (by omega)) (fun j hj => hmono j (by omega))
    have h1 : 0 < a n := hpos n (by omega)
    have h2 : 0 < a (n + 1) := hpos (n + 1) le_rfl
    have hl := Real.log_le_sub_one_of_pos (div_pos h2 h1)
    rw [Real.log_div h2.ne' h1.ne'] at hl
    have : (a n - a (n + 1)) / a n = 1 - a (n + 1) / a n := by field_simp
    linarith

theorem sum_bound (a : ℕ → ℝ) (n : ℕ) (ε M : ℝ) (hε : 0 < ε) (hεM : ε ≤ M)
    (hpos : ∀ j < n, ε ≤ a j) (hlast : 0 ≤ a n) (hmono : ∀ j < n, a (j + 1) ≤ a j)
    (h0 : a 0 ≤ M) :
    ∑ j ∈ Finset.range n, (a j - a (j + 1)) / a j ≤ 1 + Real.log (M / ε) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
    have : 1 ≤ M / ε := by rw [le_div_iff₀ hε]; linarith
    have := Real.log_nonneg this
    linarith
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ]
  have ht := tele a k (fun j hj => lt_of_lt_of_le hε (hpos j (by omega)))
    (fun j hj => hmono j (by omega))
  have hk : ε ≤ a k := hpos k (by omega)
  have hk0 : 0 < a k := lt_of_lt_of_le hε hk
  have hlastle : (a k - a (k + 1)) / a k ≤ 1 := by
    rw [div_le_one hk0]; linarith
  have ha0 : 0 < a 0 := lt_of_lt_of_le hε (hpos 0 (by omega))
  have hlog1 : Real.log (a 0) ≤ Real.log M := Real.log_le_log ha0 h0
  have hlog2 : Real.log ε ≤ Real.log (a k) := Real.log_le_log hε hk
  rw [Real.log_div (by linarith) hε.ne']
  linarith

end ASCL45

open ASCL45 in
theorem solution {U : Type} [Fintype U] [DecidableEq U] {m : ℕ} (I : Instance U m) (hI : I.Standing) (hQ : 0 < I.Q)
    (z : ℕ) (L : List (Fin m)) (hL : I.IsGreedyList (fun A => (I.f A : ℝ)) I.Q (I.tau z) Finset.univ L)
    (α : ℝ) (hα : 0 < α) (i : ℕ) (hi : 1 ≤ i) (ω : Fin m → U) :
    I.Gpath (I.tau z) α L i ω ≤ 1 + Real.log (1 / delta z) := by
  obtain ⟨-, -, -, hmon, -⟩ := hI
  set H := I.NA (I.tau z) L ω with hH
  set a : ℕ → ℝ := fun j => (I.Q : ℝ) - I.f (History.realized (H.take j)) with ha
  have hδ : 0 < delta z := by unfold delta; positivity
  have hδ1 : delta z ≤ 1 := by unfold delta; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hQr : (0 : ℝ) < I.Q := by exact_mod_cast hQ
  -- f ≤ Q
  have hfQ : ∀ A : Finset U, (I.f A : ℝ) ≤ I.Q := by
    intro A; unfold Instance.Q; exact_mod_cast hmon (Finset.subset_univ A)
  -- monotone along the path
  have hstep : ∀ j, (I.f (History.realized (H.take j)) : ℝ) ≤ I.f (History.realized (H.take (j + 1))) := by
    intro j
    have hsub : History.realized (H.take j) ⊆ History.realized (H.take (j + 1)) := by
      intro x hx
      simp only [History.realized, List.mem_toFinset, List.mem_map] at hx ⊢
      obtain ⟨p, hp, rfl⟩ := hx
      exact ⟨p, List.take_subset_take_left H (Nat.le_succ j) hp, rfl⟩
    exact_mod_cast hmon hsub
  -- no stop before each probe
  have hns : ∀ j < H.length, (I.f (History.realized (H.take j)) : ℝ) ≤ I.tau z := by
    intro j hj
    have := go_noStop (I.parcaRound (I.tau z) L).stop ω L [] j (by simp) hj
    simp only [Instance.parcaRound, decide_eq_false_iff_not, not_lt] at this
    simpa [hH, Instance.NA, Round.run, Instance.parcaRound] using this
  have key : I.Gpath (I.tau z) α L i ω ≤ ∑ j ∈ Finset.range H.length, (a j - a (j + 1)) / a j := by
    unfold Instance.Gpath
    rw [← hH]
    apply Finset.sum_le_sum
    intro j hj
    simp only [ha]
    set A : ℝ := (I.costOf (H.take j) : ℝ)
    set B : ℝ := (I.costOf (H.take (j + 1)) : ℝ)
    set V₀ : ℝ := (I.f (History.realized (H.take j)) : ℝ)
    set V₁ : ℝ := (I.f (History.realized (H.take (j + 1))) : ℝ)
    have hr : 0 ≤ (V₁ - V₀) / ((I.Q : ℝ) - V₀) :=
      div_nonneg (by linarith [hstep j]) (by linarith [hfQ (History.realized (H.take j))])
    have hw : max 0 (min B (α * 2 ^ i) - max A (α * 2 ^ (i - 1))) / (B - A) ≤ 1 := by
      rcases le_or_gt (B - A) 0 with hBA | hBA
      · exact (div_nonpos_of_nonneg_of_nonpos (le_max_left _ _) hBA).trans zero_le_one
      · rw [div_le_one hBA]
        apply max_le hBA.le
        have := min_le_left B (α * 2 ^ i)
        have := le_max_left A (α * 2 ^ (i - 1))
        linarith
    have e : ((I.Q : ℝ) - V₀ - ((I.Q : ℝ) - V₁)) / ((I.Q : ℝ) - V₀) = (V₁ - V₀) / ((I.Q : ℝ) - V₀) := by
      ring_nf
    show max 0 (min B (α * 2 ^ i) - max A (α * 2 ^ (i - 1))) / (B - A) * ((V₁ - V₀) / ((I.Q : ℝ) - V₀)) ≤ _
    rw [e]
    calc _ ≤ 1 * ((V₁ - V₀) / ((I.Q : ℝ) - V₀)) := mul_le_mul_of_nonneg_right hw hr
      _ = _ := one_mul _
  refine key.trans ?_
  have hb := sum_bound a H.length (delta z * I.Q) I.Q (by positivity)
    (by nlinarith) ?_ ?_ ?_ ?_
  · have : (I.Q : ℝ) / (delta z * I.Q) = 1 / delta z := by field_simp
    rw [this] at hb; exact hb
  · intro j hj
    have := hns j hj
    simp only [ha, Instance.tau] at this ⊢
    nlinarith
  · simp only [ha]; linarith [hfQ (History.realized (H.take H.length))]
  · intro j _; simp only [ha]; linarith [hstep j]
  · simp only [ha]; have : (0:ℝ) ≤ I.f (History.realized (H.take 0)) := by positivity
    linarith
