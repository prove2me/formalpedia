-- Prove2me | solution 1 for Arxiv1906_02603.burr_not_rayleigh
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T19:43:31.67484+00:00
-- url     : https://prove2.me/submissions/eeb051f2-9a11-4d15-b2e2-4bfcde168adc

import Mathlib
import Definitions.Def_Arxiv1906_02603_Basic

open MeasureTheory

open Arxiv1906_02603 in
theorem solution (lam b S : ℝ) (hlam : 0 < lam) (hb : 1 < b) (hS : 0 < S) :
    ∃ A : ℝ, 0 < A ∧ burrPdf lam b A ≠ rayleighPdf S A := by
  by_contra hcon
  push Not at hcon
  set c := 1 / lam ^ 2 with hc
  have hc0 : 0 < c := by positivity
  clear_value c
  have E : ∀ k : ℝ, 0 < k →
      2 * (b - 1) / (lam ^ 2 * (k * c + 1) ^ b) = Real.exp (-(k / (2 * S ^ 2))) / S ^ 2 := by
    intro k hk
    have h := hcon (Real.sqrt k) (Real.sqrt_pos.mpr hk)
    unfold burrPdf rayleighPdf at h
    rw [div_pow, Real.sq_sqrt hk.le] at h
    have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
    have e : k / lam ^ 2 = k * c := by rw [hc]; ring
    rw [e] at h
    have hp : 0 < (k * c + 1) ^ b := Real.rpow_pos_of_pos (by positivity) b
    have h' : Real.sqrt k * (2 * (b - 1) / (lam ^ 2 * (k * c + 1) ^ b)) =
        Real.sqrt k * (Real.exp (-(k / (2 * S ^ 2))) / S ^ 2) := by
      rw [← mul_div_assoc, ← mul_div_assoc]
      convert h using 1 <;> ring
    exact mul_left_cancel₀ hsk.ne' h'
  have E1 := E 1 one_pos
  have E2 := E 2 two_pos
  have E3 := E 3 (by norm_num)
  have hx : Real.exp (-(1 / (2 * S ^ 2))) * Real.exp (-(3 / (2 * S ^ 2))) =
      Real.exp (-(2 / (2 * S ^ 2))) ^ 2 := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have p1 : 0 < (1 * c + 1) ^ b := Real.rpow_pos_of_pos (by positivity) b
  have p2 : 0 < (2 * c + 1) ^ b := Real.rpow_pos_of_pos (by positivity) b
  have p3 : 0 < (3 * c + 1) ^ b := Real.rpow_pos_of_pos (by positivity) b
  have hb1 : 0 < b - 1 := by linarith
  have key : (1 * c + 1) ^ b * (3 * c + 1) ^ b = ((2 * c + 1) ^ b) ^ 2 := by
    have : (2 * (b - 1) / (lam ^ 2 * (1 * c + 1) ^ b)) * (2 * (b - 1) / (lam ^ 2 * (3 * c + 1) ^ b))
        = (2 * (b - 1) / (lam ^ 2 * (2 * c + 1) ^ b)) ^ 2 := by
      rw [E1, E2, E3, div_pow, ← hx]; ring
    field_simp at this
    ring_nf at this ⊢
    linarith
  rw [← Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity), mul_comm b, Real.rpow_mul (by positivity),
    Real.rpow_natCast] at key
  have := (Real.rpow_left_inj (by positivity) (by positivity) (by linarith : b ≠ 0)).mp key
  nlinarith [mul_pos hc0 hc0]
