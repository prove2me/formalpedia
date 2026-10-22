-- Prove2me | solution 1 for AcquihiringMonopsony.PrivateInfo.profit_comparison_roots
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:05:27.694754+00:00
-- url     : https://prove2.me/submissions/166f6c5f-e76d-49c1-9779-619dc037a573

import Mathlib
import Definitions.Def_AcquihiringMonopsony_PrivateInfo_Model

set_option autoImplicit false
open AcquihiringMonopsony.PrivateInfo

theorem solution (P : Params) (hB : 0 < P.B) :
    ((P.va - P.vs + P.B) ^ 2 / (9 * P.B) < P.va - P.vs ↔
      vHat P < P.va ∧ P.va < P.vs + (7 + 3 * Real.sqrt 5) / 2 * P.B) ∧
    ((P.va - P.vs + P.B) ^ 2 / (9 * P.B) = P.va - P.vs ↔
      P.va = vHat P ∨ P.va = P.vs + (7 + 3 * Real.sqrt 5) / 2 * P.B) ∧
    P.vs + 2 * P.B < P.vs + (7 + 3 * Real.sqrt 5) / 2 * P.B := by
  set s := Real.sqrt 5 with hs
  have hs2 : s ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have hs3 : 2 < s := by nlinarith
  set x := P.va - P.vs with hx
  set x1 := (7 - 3 * s) / 2 * P.B with hx1
  set x2 := (7 + 3 * s) / 2 * P.B with hx2
  have h12 : x1 < x2 := by
    rw [hx1, hx2]; nlinarith
  have hfac : (x + P.B) ^ 2 - 9 * P.B * x = (x - x1) * (x - x2) := by
    have e : (x - x1) * (x - x2) = x ^ 2 - 7 * P.B * x + (49 - 9 * s ^ 2) / 4 * P.B ^ 2 := by
      rw [hx1, hx2]; ring
    rw [e, hs2]; ring
  have hvh : vHat P = P.vs + x1 := rfl
  have hva : P.va = P.vs + x := by rw [hx]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]
    constructor
    · intro h
      have : (x - x1) * (x - x2) < 0 := by rw [← hfac]; nlinarith
      rcases mul_neg_iff.mp this with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · constructor <;> linarith
      · linarith
    · rintro ⟨h1, h2⟩
      have : (x - x1) * (x - x2) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
      nlinarith
  · rw [div_eq_iff (by positivity)]
    constructor
    · intro h
      have : (x - x1) * (x - x2) = 0 := by rw [← hfac]; nlinarith
      rcases mul_eq_zero.mp this with h1 | h1
      · left; linarith
      · right; linarith
    · rintro (h | h)
      · have : x = x1 := by linarith
        have : (x - x1) * (x - x2) = 0 := by rw [this]; ring
        nlinarith
      · have : x = x2 := by linarith
        have : (x - x1) * (x - x2) = 0 := by rw [this]; ring
        nlinarith
  · nlinarith
