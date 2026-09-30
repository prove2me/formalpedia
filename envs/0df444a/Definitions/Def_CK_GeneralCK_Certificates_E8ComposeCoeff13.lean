-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ComposeCoeff13
-- name    : CK_GeneralCK_Certificates_E8ComposeCoeff13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:10:41.236934+00:00
-- url     : https://prove2.me/theorems/a4c2a77b-3730-4458-8fb5-531f0fd107e7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ComposeCoeff13` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ComposeCoeff13` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ComposeCoeff13` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ComposeCoeff13 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ComposeCoeff13.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ComposeCoeff11

-- ===== source module GeneralCK.Certificates.E8ComposeCoeff13 =====
section

namespace GeneralCK.Certificates.E8ComposeCoeff13

open E8AnalyticInverseRecurrence E8ComposeCoeff7 E8ComposeCoeff11

theorem p10_12 (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 10 12 = 10 * b 1 ^ 9 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, p9_11, powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p11_13 (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 11 13 = 11 * b 1 ^ 10 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, p10_12, powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p8_12 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) :
    powCoeff b 8 12 = 8 * b 1 ^ 7 * b 5 + 28 * b 1 ^ 6 * b 3 ^ 2 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, b4, p7_11, p7_9,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p9_13 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) :
    powCoeff b 9 13 = 9 * b 1 ^ 8 * b 5 + 36 * b 1 ^ 7 * b 3 ^ 2 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, b4, p8_12, p8_10,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p6_12 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) :
    powCoeff b 6 12 = 6*b 1^5*b 7 + 30*b 1^4*b 3*b 5 +
      20*b 1^3*b 3^3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, b4, b6, b8, p5_11, p5_9, p5_7,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p7_13 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) :
    powCoeff b 7 13 = 7*b 1^6*b 7 + 42*b 1^5*b 3*b 5 +
      35*b 1^4*b 3^3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, b4, b6, b8, p6_12, p6_10, p6_8,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p4_12 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) (b10 : b 10 = 0) :
    powCoeff b 4 12 = 4*b 1^3*b 9 + 12*b 1^2*b 3*b 7 +
      6*b 1^2*b 5^2 + 12*b 1*b 3^2*b 5 + b 3^4 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, b4, b6, b8, b10, p3_11, p3_9,
    p3_7, p3_5, powCoeff_zero_of_lt, powCoeff_diag]
  ring

theorem p5_13 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) (b10 : b 10 = 0) :
    powCoeff b 5 13 = 5*b 1^4*b 9 + 20*b 1^3*b 3*b 7 +
      10*b 1^3*b 5^2 + 30*b 1^2*b 3^2*b 5 + 5*b 1*b 3^4 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, b4, b6, b8, b10, p4_12, p4_10,
    p4_8, p4_6, powCoeff_zero_of_lt, powCoeff_diag]
  ring

set_option maxHeartbeats 0 in
theorem p3_13 (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) (b10 : b 10 = 0) (b12 : b 12 = 0) :
    powCoeff b 3 13 = 3*b 1^2*b 11 + 6*b 1*b 3*b 9 +
      6*b 1*b 5*b 7 + 3*b 3^2*b 7 + 3*b 3*b 5^2 := by
  simp (config := { maxSteps := 1000000 })
    [powCoeff, Finset.sum_range_succ, b0, b2, b4, b6, b8, b10, b12]
  ring

theorem composeCoeff_thirteen_odd (a b : ℕ → ℂ)
    (a2 : a 2 = 0) (a4 : a 4 = 0) (a6 : a 6 = 0)
    (a8 : a 8 = 0) (a10 : a 10 = 0)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) (b10 : b 10 = 0) (b12 : b 12 = 0) :
    composeCoeff a b 13 = a 1*b 13 +
      a 3*(3*b 1^2*b 11 + 6*b 1*b 3*b 9 + 6*b 1*b 5*b 7 +
        3*b 3^2*b 7 + 3*b 3*b 5^2) +
      a 5*(5*b 1^4*b 9 + 20*b 1^3*b 3*b 7 + 10*b 1^3*b 5^2 +
        30*b 1^2*b 3^2*b 5 + 5*b 1*b 3^4) +
      a 7*(7*b 1^6*b 7 + 42*b 1^5*b 3*b 5 + 35*b 1^4*b 3^3) +
      a 9*(9*b 1^8*b 5 + 36*b 1^7*b 3^2) +
      a 11*(11*b 1^10*b 3) + a 13*b 1^13 := by
  simp only [composeCoeff, Finset.sum_range_succ]
  rw [a2, a4, a6, a8, a10]
  simp only [zero_mul, add_zero]
  rw [powCoeff_one, p3_13 b b0 b2 b4 b6 b8 b10 b12,
    p5_13 b b0 b2 b4 b6 b8 b10, p7_13 b b0 b2 b4 b6 b8,
    p9_13 b b0 b2 b4, p11_13 b b0 b2,
    powCoeff_next_diag_zero b b0 b2 12, powCoeff_diag b b0 13]
  simp [powCoeff]

end GeneralCK.Certificates.E8ComposeCoeff13

end


