-- Prove2me | Definitions.Def_dusart_psi_433_20261014_CountingMarginTail
-- name    : dusart_psi_433_20261014_CountingMarginTail
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:18:58.733982+00:00
-- url     : https://prove2.me/theorems/904b85fa-0fd3-4cb7-8ee5-fc880a5010d3
-- title:
--   Dusart smoothing: Counting Margin Tail
-- statement:
--   This module gives the complete counting margin tail component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_Parameters
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
namespace DusartSmoothing
open Real Set

lemma counting_error_numerical_margin_with_tail (X : ℝ) (hX : (836 / 100 : ℝ) < X) :
    (257 / 100 : ℝ) * (9 * X + 81) * (X + 2) * Real.exp (-X) < 98 / 100 := by
  let f : ℝ → ℝ := fun y => (9 * y + 81) * (y + 2) * Real.exp (-y)
  have hd : ∀ y : ℝ, HasDerivAt f
      ((-9 * y^2 - 81 * y - 63) * Real.exp (-y)) y := by
    intro y
    convert (((((hasDerivAt_id y).const_mul 9).add_const 81).mul
      ((hasDerivAt_id y).add_const 2)).mul ((hasDerivAt_id y).neg.exp)) using 1 <;> try rfl
    dsimp
    ring
  have hmono : AntitoneOn f (Set.Ici (836 / 100 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) (by dsimp [f]; fun_prop)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt)
    intro y hy
    rw [(hd y).deriv]
    have hy' : (836 / 100 : ℝ) < y := by simpa only [interior_Ici, mem_Ioi] using hy
    exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (Real.exp_nonneg _)
  have hexp : (4262 : ℝ) < Real.exp (836 / 100 : ℝ) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 836 / 100) 30
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have hbase : (257 / 100 : ℝ) * f (836 / 100 : ℝ) < 98 / 100 := by
    dsimp [f]
    rw [Real.exp_neg, ← mul_assoc, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (Real.exp_pos _)).2
    norm_num
    linarith
  have hf := hmono (by simp) (Set.mem_Ici.mpr hX.le) hX.le
  have h := (mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 257 / 100)).trans_lt hbase
  convert h using 1 <;> try rfl
  dsimp [f]
  ring

end DusartSmoothing


