-- Prove2me | Definitions.Def_SZ_ThmC
-- name    : SZ_ThmC
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:47:49.50944+00:00
-- url     : https://prove2.me/theorems/a4fcf7ed-78da-4fa3-b7a7-359a358aa78c
-- title:
--   Thm C
-- statement:
--   Definitions and structural lemmas for Thm C, from Ralf Stephan (rwst/Square-Roots; see pinned CC0-1.0 LICENSE and source headers)'s pinned Even integral parts of powers of square roots and Dubickas Problem 3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/ThmC.lean

import Definitions.Def_SZ_SliceHygiene
import Mathlib.Tactic.Push
import Mathlib.Tactic.IntervalCases
set_option autoImplicit false
namespace SZ
theorem p_le_sqrt {p : ℤ} {m : ℕ} (hp : 0 ≤ p) (h : p ^ 2 ≤ (m : ℤ)) :
    (p : ℝ) ≤ Real.sqrt m := by
  have hpr : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hc : ((p : ℝ)) ^ 2 ≤ (m : ℝ) := by exact_mod_cast h
  have h2 := Real.sqrt_le_sqrt hc
  rwa [Real.sqrt_sq hpr] at h2
theorem p_lt_sqrt {p : ℤ} {m : ℕ} (hp : 0 ≤ p) (h : p ^ 2 < (m : ℤ)) :
    (p : ℝ) < Real.sqrt m := by
  have hpr : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hc : ((p : ℝ)) ^ 2 < (m : ℝ) := by exact_mod_cast h
  have h2 : Real.sqrt (((p : ℝ)) ^ 2) < Real.sqrt m :=
    Real.sqrt_lt_sqrt (by positivity) hc
  rwa [Real.sqrt_sq hpr] at h2
theorem sq_lt_of_window {p : ℤ} {m : ℕ} (hp : 2 ≤ p) (hm : 3 ≤ m) (hd : p ∣ (m : ℤ))
    (hU : (p : ℝ) * ((m : ℝ) - 1) < ((m : ℝ) - (p : ℝ)) * (1 + Real.sqrt m)) :
    p ^ 2 < (m : ℤ) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hm3 : (3 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  have hk1 : 1 ≤ k := by nlinarith
  have hkp : k ≤ p := by nlinarith
  -- the real-valued shadow of the integer data
  have hpr : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hkpr : (k : ℝ) ≤ (p : ℝ) := by exact_mod_cast hkp
  have hmr : (m : ℝ) = (p : ℝ) * (k : ℝ) := by exact_mod_cast hk
  have hs : Real.sqrt m ≤ (p : ℝ) := by
    have h2 : Real.sqrt m ≤ Real.sqrt (((p : ℝ)) ^ 2) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hcon)
    rwa [Real.sqrt_sq (by linarith)] at h2
  have hs0 : (0 : ℝ) ≤ Real.sqrt m := Real.sqrt_nonneg _
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (p : ℝ))
      (by linarith : (0:ℝ) ≤ (k : ℝ) - 1)) (by linarith : (0:ℝ) ≤ (p : ℝ) - Real.sqrt m),
    mul_nonneg (by linarith : (0:ℝ) ≤ (p : ℝ)) (by linarith : (0:ℝ) ≤ (p : ℝ) - (k : ℝ))]
noncomputable def sliceOne (p : ℤ) (m : ℕ) (hp : 2 ≤ p) (hm : 3 ≤ m) (hns : ¬ IsSquare m)
    (hd : p ∣ (m : ℤ) - 1) (hpm : p ^ 2 ≤ (m : ℤ)) : Slice where
  m := m
  p := p
  e := (m : ℤ) - 1
  U := 1 + Real.sqrt m
  three_le := hm
  not_square := hns
  two_le_p := hp
  p_le_e := by
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ p - 2) (by omega : (0:ℤ) ≤ p)]
  p_dvd_e := hd
  e_le := le_refl _
  U_def := by push_cast; ring
  p_le_U := by
    have := p_le_sqrt (show (0:ℤ) ≤ p by omega) hpm
    linarith
  gap := by
    have hs := p_le_sqrt (show (0:ℤ) ≤ p by omega) hpm
    have hs2 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (by positivity)
    have hs0 : (0 : ℝ) ≤ Real.sqrt m := Real.sqrt_nonneg _
    push_cast
    nlinarith
noncomputable def sliceTwo (p : ℤ) (m : ℕ) (hp : 2 ≤ p) (hm : 3 ≤ m) (hns : ¬ IsSquare m)
    (hd : p ∣ (m : ℤ))
    (hU : (p : ℝ) * ((m : ℝ) - 1) < ((m : ℝ) - (p : ℝ)) * (1 + Real.sqrt m)) : Slice where
  m := m
  p := p
  e := (m : ℤ) - p
  U := ((m : ℝ) - (p : ℝ)) * (1 + Real.sqrt m) / ((m : ℝ) - 1)
  three_le := hm
  not_square := hns
  two_le_p := hp
  p_le_e := by
    have h := sq_lt_of_window hp hm hd hU
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ p - 2) (by omega : (0:ℤ) ≤ p)]
  p_dvd_e := dvd_sub hd dvd_rfl
  e_le := by omega
  U_def := by
    have hm1 : ((m : ℝ) - 1) ≠ 0 := by
      have : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      intro h; linarith
    field_simp
    push_cast
    ring
  p_le_U := by
    have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
      have : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    rw [le_div_iff₀ hm1]
    linarith
  gap := by
    have h := sq_lt_of_window hp hm hd hU
    have hs := p_lt_sqrt (show (0:ℤ) ≤ p by omega) h
    have hs2 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (by positivity)
    have hs0 : (0 : ℝ) ≤ Real.sqrt m := Real.sqrt_nonneg _
    have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
      have : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hpU : (p : ℝ) ≤ ((m : ℝ) - (p : ℝ)) * (1 + Real.sqrt m) / ((m : ℝ) - 1) := by
      rw [le_div_iff₀ hm1]; linarith
    push_cast
    nlinarith
end SZ


