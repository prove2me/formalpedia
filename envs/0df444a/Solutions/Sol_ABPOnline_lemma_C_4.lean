-- Prove2me | solution 1 for ABPOnline.lemma_C_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:02:27.933421+00:00
-- url     : https://prove2.me/submissions/e455c626-c9c1-4fa0-a80f-1950a41e1251

import Mathlib

set_option autoImplicit false

theorem solution (L : ℕ) (e Pseq θ : ℕ → ℝ) (he0 : e 0 = 0) (hP0 : Pseq 0 = 0)
    (hrec : ∀ n < L, e (n + 1) = θ n * e n + (Pseq (n + 1) - Pseq n))
    (hθ : ∀ n < L, 0 ≤ θ n ∧ θ n ≤ 1) :
    (Finset.range (L + 1)).sup' Finset.nonempty_range_add_one (fun n => |e n|) ≤
      2 * (Finset.range (L + 1)).sup' Finset.nonempty_range_add_one (fun n => |Pseq n|) := by
  set B := (Finset.range (L + 1)).sup' Finset.nonempty_range_add_one (fun n => |Pseq n|) with hB
  have hPB : ∀ n ≤ L, |Pseq n| ≤ B := fun n hn =>
    Finset.le_sup' (fun n => |Pseq n|) (Finset.mem_range.mpr (by omega))
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hPB 0 (Nat.zero_le _))
  have hsub : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := by
    intro x y
    have := abs_add_le x (-y)
    rwa [abs_neg, ← sub_eq_add_neg] at this
  have hf : ∀ n ≤ L, |e n - Pseq n| ≤ B := by
    intro n
    induction n with
    | zero => intro _; rw [he0, hP0, sub_self, abs_zero]; exact hB0
    | succ n ih =>
      intro hn
      have hnL : n < L := by omega
      have ih' := ih (by omega)
      obtain ⟨h0, h1⟩ := hθ n hnL
      have e1 : e (n + 1) - Pseq (n + 1) = θ n * (e n - Pseq n) - (1 - θ n) * Pseq n := by
        rw [hrec n hnL]; ring
      rw [e1]
      have h2 : |θ n * (e n - Pseq n) - (1 - θ n) * Pseq n| ≤
          θ n * |e n - Pseq n| + (1 - θ n) * |Pseq n| := by
        refine (hsub _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg (sub_nonneg.mpr h1)]
      have h3 := mul_le_mul_of_nonneg_left ih' h0
      have h4 := mul_le_mul_of_nonneg_left (hPB n (by omega)) (sub_nonneg.mpr h1)
      nlinarith
  apply Finset.sup'_le
  intro n hn
  have hnL : n ≤ L := by have := Finset.mem_range.mp hn; omega
  have : |e n| ≤ |e n - Pseq n| + |Pseq n| := by
    have := abs_add_le (e n - Pseq n) (Pseq n)
    rwa [sub_add_cancel] at this
  linarith [hf n hnL, hPB n hnL]
