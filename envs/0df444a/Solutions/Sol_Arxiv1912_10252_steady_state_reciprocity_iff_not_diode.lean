-- Prove2me | solution 1 for Arxiv1912_10252.steady_state_reciprocity_iff_not_diode
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T19:42:20.970299+00:00
-- url     : https://prove2.me/submissions/4684ab8d-2ace-4bd8-95c8-94d02d415bdd

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

theorem rec_not_diode (s : TwoPortData) (hkc : 0 < s.kc) (hsigma : 0 < s.sigma)
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

lemma not_diode_rec (s : TwoPortData) (hkc : 0 < s.kc) (hsigma : 0 < s.sigma)
    (hL : 0 < s.L) (hQ0 : s.Q0 ≠ 0) (hE : EnergyConservation s) (hG : (greenMat s).det ≠ 0)
    (hnd : IsNotDiode s) : IsGloballyReciprocal s := by
  obtain ⟨ha, hb⟩ := energy_balance_aux s hkc hsigma hL hE
  have hL0 : s.L ≠ 0 := hL.ne'
  have hdet : (greenMat s).det = s.L ^ 2 * (s.C1b * s.C2a - s.C1a * s.C2b) := by
    simp [greenMat, Matrix.det_fin_two]; ring
  rw [hdet] at hG
  have hD : s.C1b * s.C2a - s.C1a * s.C2b ≠ 0 := fun h => hG (by rw [h]; ring)
  set k : ℝ := 1 / (s.L * (s.C1b * s.C2a - s.C1a * s.C2b)) with hk
  have hkL : s.L * (s.C1b * s.C2a - s.C1a * s.C2b) * k = 1 := by
    rw [hk]; field_simp
  have hk0 : k ≠ 0 := by intro h; rw [h, mul_zero] at hkL; exact zero_ne_one hkL
  have hf : (greenMat s).mulVec ![-s.C2b * k, s.C2a * k] = ![1, 0] := by
    funext i; fin_cases i
    · simp [greenMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; linear_combination hkL
    · simp [greenMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  have hf' : (greenMat s).mulVec ![-s.C1b * k, s.C1a * k] = ![0, 1] := by
    funext i; fin_cases i
    · simp [greenMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
    · simp [greenMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; linear_combination hkL
  have c := congrFun (hnd 1 0 _ _ hf hf') 1
  simp [fluxMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at c
  have hkk : s.kc * k ≠ 0 := mul_ne_zero hkc.ne' hk0
  have c2 : s.kc * k * (s.D2b * s.C1a - s.D1a * s.C2b) = 0 := by linear_combination c
  have c3 := (mul_eq_zero.mp c2).resolve_left hkk
  have c4 : (s.C1b + s.C2a) * (s.C1a - s.D1a) = 0 := by
    have hd2 : s.D2b = s.C1b + s.C2a - s.D1a := by linarith
    have hc2 : s.C2b = s.C1b - s.C1a + s.C2a := by linarith
    rw [hd2, hc2] at c3; linear_combination c3
  unfold IsGloballyReciprocal
  simp only [greenMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.head_fin_const]
  rcases mul_eq_zero.mp c4 with h | h
  · linear_combination s.L * h
  · exfalso
    obtain ⟨h1, -, h3, -⟩ := hE
    have : s.D1a = s.C1a := by linarith
    rw [this] at h1
    apply hQ0; linarith

theorem solution (s : TwoPortData) (hkc : 0 < s.kc)
    (hsigma : 0 < s.sigma) (hL : 0 < s.L) (hQ0 : s.Q0 ≠ 0) (hE : EnergyConservation s)
    (hG : (greenMat s).det ≠ 0) :
    IsNotDiode s ↔ IsGloballyReciprocal s :=
  ⟨not_diode_rec s hkc hsigma hL hQ0 hE hG,
   fun h => (rec_not_diode s hkc hsigma hL hQ0 hE hG h).2.2.2⟩

