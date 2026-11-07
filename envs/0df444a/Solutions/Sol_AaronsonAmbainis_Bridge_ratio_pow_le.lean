-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.ratio_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:33.261818+00:00
-- url     : https://prove2.me/submissions/4364f060-dd5b-4713-aa08-bfe70ec35aa3

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {ε D I : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hD : 1 ≤ D) (hI : 0 ≤ I)
    (h : 192 * ε ^ 5 ≤ 3125 * Real.pi ^ 8 * D ^ 12 * I ^ 2) : (ε / D) ^ 7 ≤ I := by
  have hD0 : 0 < D := lt_of_lt_of_le one_pos hD
  apply le_of_pow_le_pow_left₀ two_ne_zero hI
  have h1 : ε ^ 9 ≤ (1 / 4) ^ 9 := pow_le_pow_left₀ hε.le hε4 9
  have hpi : Real.pi ^ 8 ≤ (3.15 : ℝ) ^ 8 :=
    pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 8
  have hB : 3125 * Real.pi ^ 8 * ε ^ 9 ≤ 192 := by
    have h4 : 3125 * Real.pi ^ 8 * ε ^ 9 ≤ 3125 * (3.15 : ℝ) ^ 8 * (1 / 4) ^ 9 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpi (by norm_num)) h1 (by positivity)
        (by positivity)
    have h5 : 3125 * (3.15 : ℝ) ^ 8 * (1 / 4) ^ 9 ≤ 192 := by norm_num
    linarith
  have hD12 : D ^ 12 ≤ D ^ 14 := pow_le_pow_right₀ hD (by norm_num)
  have hc : 0 < 3125 * Real.pi ^ 8 := by positivity
  have h6 : (3125 * Real.pi ^ 8) * ε ^ 14 ≤ (3125 * Real.pi ^ 8) * (D ^ 14 * I ^ 2) := by
    calc (3125 * Real.pi ^ 8) * ε ^ 14 = (3125 * Real.pi ^ 8 * ε ^ 9) * ε ^ 5 := by ring
      _ ≤ 192 * ε ^ 5 := mul_le_mul_of_nonneg_right hB (by positivity)
      _ ≤ 3125 * Real.pi ^ 8 * D ^ 12 * I ^ 2 := h
      _ ≤ 3125 * Real.pi ^ 8 * D ^ 14 * I ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD12 hc.le) (sq_nonneg I)
      _ = (3125 * Real.pi ^ 8) * (D ^ 14 * I ^ 2) := by ring
  have h7 : ε ^ 14 ≤ D ^ 14 * I ^ 2 := le_of_mul_le_mul_left h6 hc
  have e : ((ε / D) ^ 7) ^ 2 = ε ^ 14 / D ^ 14 := by
    rw [← pow_mul, div_pow]
  rw [e, div_le_iff₀ (pow_pos hD0 14)]
  linarith
end AaronsonAmbainis.Bridge
