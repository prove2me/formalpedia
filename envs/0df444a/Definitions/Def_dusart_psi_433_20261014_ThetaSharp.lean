-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ThetaSharp
-- name    : dusart_psi_433_20261014_ThetaSharp
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:23:11.731553+00:00
-- url     : https://prove2.me/theorems/d598fc4b-be3f-4c51-ab2e-c16968e6bed1
-- title:
--   Dusart smoothing: Theta Sharp
-- statement:
--   This module gives the complete theta sharp component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_LowHeight
noncomputable section
namespace DusartSmoothing.LowHeight
open Complex Real Set MeasureTheory

lemma exp_neg_nine_lt : Real.exp (-9) < (1 / 8000 : ℝ) := by
  have h3 : (20 : ℝ) < Real.exp 3 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 9
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have he : Real.exp 9 = (Real.exp 3) ^ 3 := by
    rw [show (9 : ℝ) = (3 : ℕ) * 3 by norm_num, Real.exp_nat_mul]
  have h9 : (8000 : ℝ) < Real.exp 9 := by
    rw [he]
    have hs : (400 : ℝ) < (Real.exp 3)^2 := by nlinarith
    have hm := mul_lt_mul_of_pos_right hs (Real.exp_pos 3)
    nlinarith
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_lt_iff₀ (Real.exp_pos 9)).2
  linarith

lemma theta_kernel_sharp (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ HurwitzZeta.evenKernel 0 x - 1 ∧
    HurwitzZeta.evenKernel 0 x - 1 ≤ (2001 / 1000 : ℝ) * Real.exp (-Real.pi * x) := by
  have hx0 : 0 < x := by linarith
  have hθ : HasSum (fun n : ℕ => 2 * Real.exp (-Real.pi * (n + 1 : ℝ)^2 * x))
      (HurwitzZeta.evenKernel 0 x - 1) := by
    simpa [zero_mul, mul_zero, Real.cos_zero, mul_one,
      HurwitzZeta.evenKernel_eq_cosKernel_of_zero] using
      HurwitzZeta.hasSum_nat_cosKernel₀ 0 hx0
  let q := Real.exp (-3 * Real.pi * x)
  have hq0 : 0 < q := Real.exp_pos _
  have hq : q < (1 / 8000 : ℝ) := by
    apply lt_of_le_of_lt (Real.exp_le_exp.mpr ?_) exp_neg_nine_lt
    have hπ := Real.pi_gt_three
    nlinarith
  have hq1 : q < 1 := by linarith
  have hgeo := (hasSum_geometric_of_lt_one hq0.le hq1).mul_left
    (2 * Real.exp (-Real.pi * x))
  have hterm : ∀ n : ℕ, 2 * Real.exp (-Real.pi * (n + 1 : ℝ)^2 * x) ≤
      (2 * Real.exp (-Real.pi * x)) * q^n := by
    intro n
    have hn : (3 * (n : ℝ) + 1) ≤ (n + 1 : ℝ)^2 := by
      by_cases hn0 : n = 0
      · subst n; norm_num
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
        nlinarith
    have he : -Real.pi * (n + 1 : ℝ)^2 * x ≤
        -Real.pi * x + (n : ℝ) * (-3 * Real.pi * x) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn) (mul_pos Real.pi_pos hx0).le]
    calc 2 * Real.exp (-Real.pi * (n + 1 : ℝ)^2 * x)
        ≤ 2 * Real.exp (-Real.pi * x + (n : ℝ) * (-3 * Real.pi * x)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) zero_le_two
      _ = _ := by rw [Real.exp_add, Real.exp_nat_mul]; dsimp [q]; ring
  have hb := hθ.summable.tsum_le_tsum hterm hgeo.summable
  rw [hθ.tsum_eq, hgeo.tsum_eq] at hb
  refine ⟨(theta_kernel_bound x hx).1, hb.trans ?_⟩
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (by linarith : 0 < 1 - q)).2
  have hexp := Real.exp_pos (-Real.pi * x)
  nlinarith

end DusartSmoothing.LowHeight


