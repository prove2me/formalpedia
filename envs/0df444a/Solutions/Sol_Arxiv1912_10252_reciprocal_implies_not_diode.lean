-- Prove2me | solution 1 for Arxiv1912_10252.reciprocal_implies_not_diode
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T19:26:01.865296+00:00
-- url     : https://prove2.me/submissions/7852a012-644c-4e4a-8ee3-2cadbc7a36b1

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
    (hL : 0 < s.L) (hQ0 : s.Q0 ≠ 0) (hE : EnergyConservation s) (hG : (greenMat s).det ≠ 0)
    (hrec : IsGloballyReciprocal s) :
    greenMat s 0 0 = greenMat s 1 1 ∧
    fluxMat s 1 0 = -fluxMat s 0 1 ∧
    fluxMat s 0 0 + fluxMat s 1 1 = 0 ∧
    IsNotDiode s := by
  obtain ⟨ha, hb⟩ := energy_balance_aux s hkc hsigma hL hE
  have hL0 : s.L ≠ 0 := hL.ne'
  unfold IsGloballyReciprocal at hrec
  simp only [greenMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.head_fin_const] at hrec
  have hbc : s.C1b = -s.C2a := by
    have : s.L * (s.C1b + s.C2a) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hL0
    linarith
  have hac : s.C1a = -s.C2b := by linarith
  have hd : s.D2b = -s.D1a := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [greenMat, hac]
  · simp [fluxMat, hbc]
  · simp [fluxMat, hd]
  · intro T1 T2 f f' hf hf'
    have e := congrFun hf 0
    have e1 := congrFun hf 1
    have e' := congrFun hf' 0
    have e1' := congrFun hf' 1
    simp [greenMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e e1 e' e1'
    -- f' is the swap of f
    have hdet : (greenMat s).det = s.L ^ 2 * (s.C1a ^ 2 - s.C1b ^ 2) := by
      simp [greenMat, Matrix.det_fin_two]; rw [hac, hbc]; ring
    rw [hdet] at hG
    have hne : s.C1a ^ 2 - s.C1b ^ 2 ≠ 0 := fun h => hG (by rw [h]; ring)
    have e1n : s.C1b * s.L * f 0 + s.C1a * s.L * f 1 = T2 := by rw [hbc, hac]; linarith
    have e1n' : s.C1b * s.L * f' 0 + s.C1a * s.L * f' 1 = T1 := by rw [hbc, hac]; linarith
    have hp : s.L * (s.C1a ^ 2 - s.C1b ^ 2) ≠ 0 :=
      mul_ne_zero hL0 hne
    have k0 : s.L * (s.C1a ^ 2 - s.C1b ^ 2) * (f' 0 - f 1) = 0 := by
      linear_combination s.C1a * (e' - e1n) - s.C1b * (e1n' - e)
    have k1 : s.L * (s.C1a ^ 2 - s.C1b ^ 2) * (f' 1 - f 0) = 0 := by
      linear_combination s.C1a * (e1n' - e) - s.C1b * (e' - e1n)
    have u : f' 0 = f 1 := by
      have := (mul_eq_zero.mp k0).resolve_left hp; linarith
    have v : f' 1 = f 0 := by
      have := (mul_eq_zero.mp k1).resolve_left hp; linarith
    funext i
    fin_cases i
    · simp [fluxMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, u, v, hd, hbc]
    · simp [fluxMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, u, v, hd, hbc]
