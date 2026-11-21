-- Prove2me | solution 1 for AlpoegeClaudeRH.DirichletL_zeros_on_line
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-21T01:30:47.533189+00:00
-- url     : https://prove2.me/submissions/799e0797-0ab9-4a8b-909d-4182eeeb3822
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Solution for AlpoegeClaudeRH.DirichletL_zeros_on_line (milestone 3),
-- as a REDUCTION to AlpoegeClaudeRH.EveryCharacter (milestone 1).
-- The target statement is the UNCONDITIONAL ∀ form (GRH for Dirichlet
-- L-functions), which cannot be proved from Mathlib alone. This file proves
-- the CONDITIONAL deduction (EveryCharacter → zeros on the line) and applies
-- the platform's Open EveryCharacter theorem as the hypothesis, so the
-- submission is a sketch: the parent auto-resolves to Proved once
-- EveryCharacter is proved. The Alpöge RH claim itself is NOT verified.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Theorems.Thm_AlpoegeClaudeRH_EveryCharacter

open Complex DirichletCharacter

theorem solution (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : DirichletCharacter.LFunction χ s = 0) :
    s.re = 1 / 2 := by
  have hgamma : ∀ {M : ℕ} (ψ : DirichletCharacter ℂ M) {t : ℂ},
      0 < t.re → gammaFactor ψ t ≠ 0 := by
    intro M ψ t ht
    rcases ψ.even_or_odd with hh | hh
    · rw [hh.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos ht
    · rw [hh.gammaFactor_def]
      exact Gammaℝ_ne_zero_of_re_pos (by rw [add_re, one_re]; linarith)
  have h : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0 :=
    AlpoegeClaudeRH.EveryCharacter
  have hs0 : s ≠ 0 := fun e => by simp [e] at h0
  have hs1 : s ≠ 1 := fun e => by simp [e] at h1
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hχ₀ : IsPrimitive χ.primitiveCharacter := χ.primitiveCharacter_isPrimitive
  have hfac : ∀ p ∈ N.primeFactors,
      (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s)) ≠ 0 := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hnorm : ‖χ.primitiveCharacter p * (p : ℂ) ^ (-s)‖ < 1 := by
      calc ‖χ.primitiveCharacter p * (p : ℂ) ^ (-s)‖
          ≤ (p : ℝ) ^ (-s).re := by
            rw [norm_mul,
              Complex.norm_natCast_cpow_of_re_ne_zero p
                (by rw [neg_re]; exact neg_ne_zero.mpr (ne_of_gt h0))]
            exact mul_le_of_le_one_left (by positivity)
              (χ.primitiveCharacter.norm_le_one _)
        _ < 1 := by
            rw [neg_re]
            exact Real.rpow_lt_one_of_one_lt_of_neg
              (by exact_mod_cast hpprime.one_lt) (by linarith)
    intro hzero
    have hz1 : χ.primitiveCharacter p * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp hzero).symm
    rw [hz1, norm_one] at hnorm
    exact lt_irrefl 1 hnorm
  have hL : DirichletCharacter.LFunction χ s =
      DirichletCharacter.LFunction χ.primitiveCharacter s *
        ∏ p ∈ N.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s)) := by
    have hcl := LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
      (Or.inr hs1)
    rwa [χ.changeLevel_primitiveCharacter] at hcl
  have hprod_ne : ∏ p ∈ N.primeFactors,
      (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfac
  have hz₀ : DirichletCharacter.LFunction χ.primitiveCharacter s = 0 := by
    rw [hL] at hz
    exact (mul_eq_zero.mp hz).resolve_right hprod_ne
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hinv : χ.primitiveCharacter⁻¹.IsPrimitive := by
      rw [isPrimitive_def, conductor_inv]; exact hχ₀
    have hc : completedLFunction χ.primitiveCharacter s = 0 := by
      rw [LFunction_eq_completed_div_gammaFactor χ.primitiveCharacter s (Or.inl hs0)]
        at hz₀
      exact (div_eq_zero_iff.1 hz₀).resolve_right
        (hgamma χ.primitiveCharacter h0)
    have hfe := hinv.completedLFunction_one_sub s
    rw [inv_inv, hc, mul_zero] at hfe
    have h2 : (1 - s) ≠ 0 := sub_ne_zero.mpr hs1.symm
    have hL0 : DirichletCharacter.LFunction χ.primitiveCharacter⁻¹ (1 - s) = 0 := by
      rw [LFunction_eq_completed_div_gammaFactor χ.primitiveCharacter⁻¹ (1 - s)
        (Or.inl h2), hfe, zero_div]
    exact h _ χ.primitiveCharacter⁻¹ (1 - s) (by rw [sub_re, one_re]; linarith)
      (Or.inr (by rw [ne_eq, sub_eq_self]; exact hs0)) hL0
  · exact h _ χ.primitiveCharacter s hgt (Or.inr hs1) hz₀
