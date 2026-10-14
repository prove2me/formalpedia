-- Prove2me | Definitions.Def_dusart_psi_433_20261014_Parameters
-- name    : dusart_psi_433_20261014_Parameters
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:16:13.031734+00:00
-- url     : https://prove2.me/theorems/9c9a1dbb-7407-4d70-99d4-593fa6377804
-- title:
--   Dusart smoothing: Parameters
-- statement:
--   This module gives the complete parameters component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace DusartSmoothing

noncomputable def X (R x : ℝ) : ℝ := Real.sqrt (Real.log x / R)

noncomputable def U (X ν : ℝ) : ℝ :=
  ν ^ 6 / (2 * ν ^ 2 - 1) *
    (1 - (Real.log (2 * Real.pi) - 1 / 2) / (X * ν)) *
    (1 - Real.log (2 * Real.pi) / (X * ν))

noncomputable def seed (X : ℝ) : ℝ :=
  1 - Real.log (X / (2 * Real.pi)) / (2 * X)

lemma log_two_pi_bounds : (1 : ℝ) ≤ Real.log (2 * Real.pi) ∧
    Real.log (2 * Real.pi) < 2 := by
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have h4 : (1 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hlow : (1 : ℝ) ≤ Real.log (2 * Real.pi) := h4.trans
    (Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_three]))
  have hexp := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at hexp
  have hhigh : Real.log (2 * Real.pi) < 2 :=
    (Real.log_lt_iff_lt_exp (by positivity)).2 (by linarith [Real.pi_lt_d2])
  exact ⟨hlow, hhigh⟩

lemma log_div_le_exp (y : ℝ) (hy : 0 < y) :
    Real.log y ≤ y / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy (Real.exp_pos 1))
  rw [Real.log_div (ne_of_gt hy) (Real.exp_ne_zero 1), Real.log_exp] at h
  linarith

lemma seed_bounds (X : ℝ) (hX : (836 / 100 : ℝ) < X) :
    (97 / 100 : ℝ) < seed X ∧ seed X < 1 := by
  have hXp : 0 < X := by linarith
  have hπ : 0 < 2 * Real.pi := by positivity
  have hy : 0 < X / (2 * Real.pi) := div_pos hXp hπ
  have hlog : 0 < Real.log (X / (2 * Real.pi)) :=
    Real.log_pos ((one_lt_div hπ).2 (by linarith [Real.pi_lt_d2]))
  have hupper := log_div_le_exp (X / (2 * Real.pi)) hy
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have hden : (100 / 3 : ℝ) < 4 * Real.pi * Real.exp 1 := by
    nlinarith [Real.pi_gt_d2, mul_nonneg
      (show 0 ≤ Real.pi - 157 / 50 by linarith [Real.pi_gt_d2])
      (show 0 ≤ Real.exp 1 - 8 / 3 by linarith)]
  have hinv : 1 / (4 * Real.pi * Real.exp 1) < (3 / 100 : ℝ) := by
    apply (div_lt_iff₀ (by positivity)).2
    linarith
  have hquot : Real.log (X / (2 * Real.pi)) / (2 * X) ≤
      1 / (4 * Real.pi * Real.exp 1) := by
    calc
      _ ≤ (X / (2 * Real.pi) / Real.exp 1) / (2 * X) :=
        div_le_div_of_nonneg_right hupper (by positivity)
      _ = _ := by field_simp; ring
  dsimp [seed]
  constructor
  · linarith
  · have hp := div_pos hlog (show 0 < 2 * X by positivity)
    linarith

lemma threshold_facts (R x : ℝ) (hR : 0 < R)
    (hX : max (836 / 100 : ℝ) (8 / R) < X R x) :
    (836 / 100 : ℝ) < X R x ∧ 0 < Real.log x ∧
      R * (X R x) ^ 2 = Real.log x ∧ 8 * X R x < Real.log x := by
  have h836 := (max_lt_iff.mp hX).1
  have h8 := (max_lt_iff.mp hX).2
  have hXp : 0 < X R x := by linarith
  have hquot : 0 < Real.log x / R := by
    have hs : 0 < Real.sqrt (Real.log x / R) := hXp
    exact Real.sqrt_pos.mp hs
  have hlog : 0 < Real.log x := (div_pos_iff.mp hquot).elim
    (fun h => h.1) (fun h => False.elim ((not_lt_of_ge hR.le) h.2))
  have hsq : (X R x) ^ 2 = Real.log x / R := Real.sq_sqrt hquot.le
  have hid : R * (X R x) ^ 2 = Real.log x := by
    rw [hsq]
    field_simp
  have hm : 8 < X R x * R := (div_lt_iff₀ hR).mp h8
  have hm' := mul_lt_mul_of_pos_right hm hXp
  refine ⟨h836, hlog, hid, ?_⟩
  nlinarith only [hm', hid]

lemma factors_pos (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) :
    0 < 2 * ν ^ 2 - 1 ∧
      0 < 1 - (Real.log (2 * Real.pi) - 1 / 2) / (X * ν) ∧
      0 < 1 - Real.log (2 * Real.pi) / (X * ν) := by
  have hXp : 0 < X := by linarith
  have hνp : 0 < ν := by linarith
  have hmul : 2 < X * ν := by
    have hm := mul_pos (show 0 < X - 836 / 100 by linarith)
      (show 0 < ν - 97 / 100 by linarith)
    nlinarith
  have ha := log_two_pi_bounds
  have hf1 : (Real.log (2 * Real.pi) - 1 / 2) / (X * ν) < 1 :=
    (div_lt_one (by positivity)).2 (by linarith)
  have hf2 : Real.log (2 * Real.pi) / (X * ν) < 1 :=
    (div_lt_one (by positivity)).2 (by linarith)
  exact ⟨by nlinarith, by linarith, by linarith⟩

lemma U_pos (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) : 0 < U X ν := by
  have hf := factors_pos X ν hX hν hν1
  have hνp : 0 < ν := by linarith
  dsimp [U]
  exact mul_pos (mul_pos (div_pos (pow_pos hνp _) hf.1) hf.2.1) hf.2.2

lemma U_at_one (X : ℝ) :
    U X 1 = (1 - (Real.log (2 * Real.pi) - 1 / 2) / X) *
      (1 - Real.log (2 * Real.pi) / X) := by
  norm_num [U]

lemma U_at_one_pos (X : ℝ) (hX : (836 / 100 : ℝ) < X) : 0 < U X 1 :=
  U_pos X 1 hX (by norm_num) (by norm_num)

lemma zero_real_part_bound (R : ℝ)
    (hzero : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0)
    (ρ : ℂ) (hρ : riemannZeta ρ = 0) (ht : 2 * Real.pi < |ρ.im|) :
    ρ.re ≤ 1 - 1 / (R * Real.log |ρ.im|) := by
  apply le_of_not_gt
  intro hσ
  exact hzero ρ ht hσ hρ

lemma zero_power_majorant (R x : ℝ) (hR : 0 < R) (hx : 0 < x) (hx1 : 1 < x)
    (hzero : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0)
    (ρ : ℂ) (hρ : riemannZeta ρ = 0) (ht : 2 * Real.pi < |ρ.im|) :
    ‖(x : ℂ) ^ ρ‖ / x ≤ Real.exp (-(X R x) ^ 2 / Real.log |ρ.im|) := by
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogt : 0 < Real.log |ρ.im| :=
    Real.log_pos (by linarith [Real.pi_gt_three])
  have hβ := zero_real_part_bound R hzero ρ hρ ht
  have hsq : (X R x) ^ 2 = Real.log x / R :=
    Real.sq_sqrt (div_nonneg hlogx.le hR.le)
  have hidentity : Real.log x * (1 - 1 / (R * Real.log |ρ.im|) - 1) =
      -(X R x) ^ 2 / Real.log |ρ.im| := by
    rw [hsq]
    field_simp [hR.ne', hlogt.ne']
    ring
  have hexponent : Real.log x * (ρ.re - 1) ≤
      -(X R x) ^ 2 / Real.log |ρ.im| := by
    calc
      _ ≤ Real.log x * (1 - 1 / (R * Real.log |ρ.im|) - 1) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right hβ 1) hlogx.le
      _ = _ := hidentity
  calc
    ‖(x : ℂ) ^ ρ‖ / x = Real.exp (Real.log x * ρ.re) / Real.exp (Real.log x) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Real.rpow_def_of_pos hx,
        Real.exp_log hx]
    _ = Real.exp (Real.log x * (ρ.re - 1)) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hexponent

lemma exists_positive_smoothing_parameter (X : ℝ) (hX : (836 / 100 : ℝ) < X) :
    ∃ ν : ℝ, (97 / 100 : ℝ) < ν ∧ ν < 1 ∧ 0 < U X ν := by
  have hs := seed_bounds X hX
  exact ⟨seed X, hs.1, hs.2, U_pos X (seed X) hX hs.1 hs.2.le⟩

end DusartSmoothing


