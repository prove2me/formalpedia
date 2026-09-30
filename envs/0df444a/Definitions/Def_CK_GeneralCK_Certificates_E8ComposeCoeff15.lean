-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ComposeCoeff15
-- name    : CK_GeneralCK_Certificates_E8ComposeCoeff15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:15:45.96179+00:00
-- url     : https://prove2.me/theorems/8f178987-48d8-4611-a684-987cc52ff972
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ComposeCoeff15` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ComposeCoeff15` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ComposeCoeff15` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ComposeCoeff15 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ComposeCoeff15.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ComposeCoeff13

-- ===== source module GeneralCK.Certificates.E8ComposeCoeff15 =====
section

namespace GeneralCK.Certificates.E8ComposeCoeff15

open E8AnalyticInverseRecurrence E8ComposeCoeff7 E8ComposeCoeff11 E8ComposeCoeff13

theorem p12_14 (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 12 14 = 12 * b 1 ^ 11 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, p11_13, powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p13_15 (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 13 15 = 13 * b 1 ^ 12 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, p12_14, powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p10_14 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) :
    powCoeff b 10 14 = 10*b 1^9*b 5 + 45*b 1^8*b 3^2 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, b4, p9_13, p9_11,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p11_15 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) :
    powCoeff b 11 15 = 11*b 1^10*b 5 + 55*b 1^9*b 3^2 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, b4, p10_14, p10_12,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p8_14 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) :
    powCoeff b 8 14 = 8*b 1^7*b 7 + 56*b 1^6*b 3*b 5 +
      56*b 1^5*b 3^3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, b4, b6, b8, p7_13, p7_11, p7_9,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p9_15 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) :
    powCoeff b 9 15 = 9*b 1^8*b 7 + 72*b 1^7*b 3*b 5 +
      84*b 1^6*b 3^3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, b4, b6, b8, p8_14, p8_12, p8_10,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p6_14 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) (b10 : b 10 = 0) :
    powCoeff b 6 14 = 6*b 1^5*b 9 + 30*b 1^4*b 3*b 7 +
      15*b 1^4*b 5^2 + 60*b 1^3*b 3^2*b 5 + 15*b 1^2*b 3^4 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, b4, b6, b8, b10, p5_13, p5_11, p5_9,
    p5_7, powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p7_15 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) (b10 : b 10 = 0) :
    powCoeff b 7 15 = 7*b 1^6*b 9 + 42*b 1^5*b 3*b 7 +
      21*b 1^5*b 5^2 + 105*b 1^4*b 3^2*b 5 + 35*b 1^3*b 3^4 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, b4, b6, b8, b10, p6_14, p6_12, p6_10,
    p6_8, powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p4_14 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) (b10 : b 10 = 0)
    (b12 : b 12 = 0) :
    powCoeff b 4 14 = 4*b 1^3*b 11 + 12*b 1^2*b 3*b 9 +
      12*b 1^2*b 5*b 7 + 12*b 1*b 3^2*b 7 +
      12*b 1*b 3*b 5^2 + 4*b 3^3*b 5 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, b4, b6, b8, b10, b12,
    p3_13, p3_11, p3_9, p3_7, p3_5, powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p5_15 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) (b10 : b 10 = 0)
    (b12 : b 12 = 0) :
    powCoeff b 5 15 = 5*b 1^4*b 11 + 20*b 1^3*b 3*b 9 +
      20*b 1^3*b 5*b 7 + 30*b 1^2*b 3^2*b 7 +
      30*b 1^2*b 3*b 5^2 + 20*b 1*b 3^3*b 5 + b 3^5 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, b4, b6, b8, b10, b12,
    p4_14, p4_12, p4_10, p4_8, p4_6, powCoeff_zero_of_lt, powCoeff_diag]
  ring

set_option maxHeartbeats 0 in
theorem p3_15 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) (b10 : b 10 = 0)
    (b12 : b 12 = 0) (b14 : b 14 = 0) :
    powCoeff b 3 15 = 3*b 1^2*b 13 + 6*b 1*b 3*b 11 +
      6*b 1*b 5*b 9 + 3*b 1*b 7^2 + 3*b 3^2*b 9 +
      6*b 3*b 5*b 7 + b 5^3 := by
  simp (config := { maxSteps := 1500000 })
    [powCoeff, Finset.sum_range_succ, b0, b2, b4, b6, b8, b10, b12, b14]
  ring

theorem composeCoeff_fifteen_odd (a b : ℕ → ℂ)
    (a2 : a 2 = 0) (a4 : a 4 = 0) (a6 : a 6 = 0)
    (a8 : a 8 = 0) (a10 : a 10 = 0) (a12 : a 12 = 0)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) (b10 : b 10 = 0)
    (b12 : b 12 = 0) (b14 : b 14 = 0) :
    composeCoeff a b 15 = a 1*b 15 +
      a 3*(3*b 1^2*b 13 + 6*b 1*b 3*b 11 + 6*b 1*b 5*b 9 +
        3*b 1*b 7^2 + 3*b 3^2*b 9 + 6*b 3*b 5*b 7 + b 5^3) +
      a 5*(5*b 1^4*b 11 + 20*b 1^3*b 3*b 9 + 20*b 1^3*b 5*b 7 +
        30*b 1^2*b 3^2*b 7 + 30*b 1^2*b 3*b 5^2 +
        20*b 1*b 3^3*b 5 + b 3^5) +
      a 7*(7*b 1^6*b 9 + 42*b 1^5*b 3*b 7 + 21*b 1^5*b 5^2 +
        105*b 1^4*b 3^2*b 5 + 35*b 1^3*b 3^4) +
      a 9*(9*b 1^8*b 7 + 72*b 1^7*b 3*b 5 + 84*b 1^6*b 3^3) +
      a 11*(11*b 1^10*b 5 + 55*b 1^9*b 3^2) +
      a 13*(13*b 1^12*b 3) + a 15*b 1^15 := by
  simp only [composeCoeff, Finset.sum_range_succ]
  rw [a2, a4, a6, a8, a10, a12]
  simp only [zero_mul, add_zero]
  rw [powCoeff_one, p3_15 b b0 b2 b4 b6 b8 b10 b12 b14,
    p5_15 b b0 b2 b4 b6 b8 b10 b12, p7_15 b b0 b2 b4 b6 b8 b10,
    p9_15 b b0 b2 b4 b6 b8, p11_15 b b0 b2 b4, p13_15 b b0 b2,
    powCoeff_next_diag_zero b b0 b2 14, powCoeff_diag b b0 15]
  simp [powCoeff]

end GeneralCK.Certificates.E8ComposeCoeff15

end


