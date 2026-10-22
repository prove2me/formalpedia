-- Prove2me | solution 1 for AgencyPassThrough.Pricing.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:32:17.837165+00:00
-- url     : https://prove2.me/submissions/1e6edab2-70bb-4702-8f62-387e8fa7f4d8

import Mathlib
import Definitions.Def_AgencyPassThrough_Pricing_Model
set_option autoImplicit false

open AgencyPassThrough.Pricing

theorem solution (n : ℕ) (hn : 2 ≤ n) (eps a b : ℝ)
    (heps0 : 0 ≤ eps) (heps1 : eps < 1) (hab : 0 < a - eps * b) :
    thetaW n eps a b - thetaB eps =
      (1 - eps) * ((n : ℝ) - 1 + eps) * b / (a - eps * b) ∧
    (thetaW n eps a b < thetaB eps ↔ b < 0) ∧
    (0 ≤ b → thetaB eps ≤ thetaW n eps a b) := by
  have h1 : 0 < 1 - eps := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hc : 0 < (n : ℝ) - 1 + eps := by linarith
  have hdiff : thetaW n eps a b - thetaB eps =
      (1 - eps) * ((n : ℝ) - 1 + eps) * b / (a - eps * b) := by
    unfold thetaW thetaB
    field_simp
    ring
  refine ⟨hdiff, ?_, ?_⟩
  · have hpos : 0 < (1 - eps) * ((n : ℝ) - 1 + eps) := mul_pos h1 hc
    constructor
    · intro h
      have : thetaW n eps a b - thetaB eps < 0 := by linarith
      rw [hdiff, div_neg_iff] at this
      rcases this with ⟨_, h2⟩ | ⟨h2, _⟩
      · linarith
      · by_contra hb
        push_neg at hb
        have := mul_nonneg hpos.le hb
        linarith
    · intro hb
      have : thetaW n eps a b - thetaB eps < 0 := by
        rw [hdiff]
        apply div_neg_of_neg_of_pos _ hab
        have := mul_neg_of_pos_of_neg hpos hb
        exact this
      linarith
  · intro hb
    have : 0 ≤ thetaW n eps a b - thetaB eps := by
      rw [hdiff]
      apply div_nonneg _ hab.le
      exact mul_nonneg (mul_pos h1 hc).le hb
    linarith
