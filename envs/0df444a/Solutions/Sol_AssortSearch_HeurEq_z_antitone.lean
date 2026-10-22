-- Prove2me | solution 1 for AssortSearch.HeurEq.z_antitone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:45:56.675627+00:00
-- url     : https://prove2.me/submissions/dfc15c2a-184b-4aea-97ca-6d0c4b248a4f

import Mathlib

set_option autoImplicit false

theorem solution (lam : ℝ) (hlam : 0 < lam) :
    AntitoneOn
      (fun δ : ℝ => δ * Real.exp (-(lam * δ)) / (1 - Real.exp (-(lam * δ))))
      (Set.Ioi 0) := by
  have key : ∀ δ : ℝ, 0 < δ →
      δ * Real.exp (-(lam * δ)) / (1 - Real.exp (-(lam * δ)))
        = δ / (Real.exp (lam * δ) - 1) := by
    intro δ hδ
    have hE : 1 < Real.exp (lam * δ) := Real.one_lt_exp_iff.mpr (mul_pos hlam hδ)
    have h0 : Real.exp (lam * δ) ≠ 0 := (Real.exp_pos _).ne'
    have h1 : Real.exp (lam * δ) - 1 ≠ 0 := by linarith
    rw [Real.exp_neg]
    field_simp
  intro a ha b hb hab
  have ha' : 0 < a := ha
  have hb' : 0 < b := hb
  simp only
  rw [key a ha', key b hb']
  have hsec := convexOn_exp.secant_mono (a := 0) (x := lam * a) (y := lam * b)
    (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)
    (by positivity) (by positivity) (by nlinarith)
  simp only [Real.exp_zero, sub_zero] at hsec
  have hp : 0 < Real.exp (lam * a) - 1 := by
    have := Real.one_lt_exp_iff.mpr (mul_pos hlam ha'); linarith
  have hq : 0 < Real.exp (lam * b) - 1 := by
    have := Real.one_lt_exp_iff.mpr (mul_pos hlam hb'); linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at hsec
  rw [div_le_div_iff₀ hq hp]
  nlinarith [mul_pos hlam hp]
