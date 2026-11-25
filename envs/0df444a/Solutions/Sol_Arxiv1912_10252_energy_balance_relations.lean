-- Prove2me | solution 1 for Arxiv1912_10252.energy_balance_relations
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T19:25:59.23238+00:00
-- url     : https://prove2.me/submissions/d80b0004-6d19-4587-9bb6-090edfc863b0

import Mathlib
import Definitions.Def_Arxiv1912_10252_Basic

open Matrix Arxiv1912_10252

lemma energy_balance_aux (s : TwoPortData) (hkc : 0 < s.kc) (hsigma : 0 < s.sigma)
    (hL : 0 < s.L) (hE : EnergyConservation s) :
    s.C1a - s.C2a = s.C1b - s.C2b ∧ s.D1a + s.D2b = s.C1b + s.C2a := by
  obtain ⟨h1, h2, h3, h4⟩ := hE
  have hks : s.kc * s.sigma ≠ 0 := (mul_pos hkc hsigma).ne'
  constructor
  · have : s.kc * s.sigma * ((s.C1a - s.C2a) - (s.C1b - s.C2b)) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hks
    linarith
  · have : s.kc * s.sigma * ((s.D1a + s.D2b) - (s.C1b + s.C2a)) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hks
    linarith

theorem solution (s : TwoPortData) (hkc : 0 < s.kc) (hsigma : 0 < s.sigma)
    (hL : 0 < s.L) (hQ0 : s.Q0 ≠ 0) (hE : EnergyConservation s) :
    greenMat s 0 0 + greenMat s 1 0 = greenMat s 0 1 + greenMat s 1 1 ∧
    fluxMat s 0 1 = s.kc * greenMat s 0 1 / s.L ∧
    fluxMat s 1 0 = -(s.kc * greenMat s 1 0 / s.L) ∧
    fluxMat s 0 0 + fluxMat s 1 1 = fluxMat s 0 1 + fluxMat s 1 0 := by
  obtain ⟨ha, hb⟩ := energy_balance_aux s hkc hsigma hL hE
  have hL0 : s.L ≠ 0 := hL.ne'
  simp only [greenMat, fluxMat, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.head_fin_const, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination s.L * ha
  · field_simp
  · field_simp
  · linear_combination s.kc * hb

