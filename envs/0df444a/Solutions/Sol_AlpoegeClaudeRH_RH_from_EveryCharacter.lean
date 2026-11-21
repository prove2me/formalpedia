-- Prove2me | solution 1 for AlpoegeClaudeRH.RH_from_EveryCharacter
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-21T01:30:46.677993+00:00
-- url     : https://prove2.me/submissions/a3a58a4d-627d-42bc-a182-949c33216462

-- Solution for AlpoegeClaudeRH.RH_from_EveryCharacter (milestone 2).
-- Target (platform, verified via API): the explicit implication
--   (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
--     1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0)
--   → ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2
-- Proved by the archive's argument (trivial character at N = 1 + reflection
-- through the completed zeta function). The Alpöge RH claim itself is NOT
-- verified; this only proves the implication from the (unproved) hypothesis.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

theorem solution
    (h : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0)
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) (hz : riemannZeta s = 0) :
    s.re = 1 / 2 := by
  have hzeta : ∀ t : ℂ, 1 / 2 < t.re → t ≠ 1 → riemannZeta t ≠ 0 := by
    intro t ht h1
    have hL := h 1 1 t ht (Or.inr h1)
    rwa [DirichletCharacter.LFunction_modOne_eq] at hL
  have hs0' : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hz
    norm_num at hz
  have hne1 : s ≠ 1 := by
    intro e
    rw [e] at hs1
    simp at hs1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1s : (1 - s) ≠ 1 := fun e => hs0' (sub_eq_self.mp e)
    have hz1 : riemannZeta (1 - s) ≠ 0 :=
      hzeta (1 - s) (by rw [Complex.sub_re, Complex.one_re]; linarith) h1s
    have hc : completedRiemannZeta s = completedRiemannZeta (1 - s) :=
      (completedRiemannZeta_one_sub s).symm
    have h1s0 : (1 - s) ≠ 0 := fun e => hne1 (sub_eq_zero.mp e).symm
    rw [riemannZeta_def_of_ne_zero hs0', div_eq_zero_iff] at hz
    rcases hz with hz | hz
    · exact hz1 (by rw [riemannZeta_def_of_ne_zero h1s0, ← hc, hz, zero_div])
    · obtain ⟨n, hn'⟩ := Complex.Gammaℝ_eq_zero_iff.1 hz
      rcases n with _ | n
      · exact hs0' (by simpa using hn')
      · have hre : s.re = -2 * ((n : ℝ) + 1) := by
          rw [hn']
          simp [Complex.mul_re]
        have hnpos : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
  · exact hzeta s hgt hne1 hz
