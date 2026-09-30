-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ComposeCoeff9
-- name    : CK_GeneralCK_Certificates_E8ComposeCoeff9
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:51:42.84516+00:00
-- url     : https://prove2.me/theorems/91190400-947d-4bde-9bd2-a55df11ecafa
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ComposeCoeff9` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ComposeCoeff9` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ComposeCoeff9` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ComposeCoeff9 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ComposeCoeff9.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ComposeCoeff7

-- ===== source module GeneralCK.Certificates.E8ComposeCoeff9 =====
section

namespace GeneralCK.Certificates.E8ComposeCoeff9

open E8AnalyticInverseRecurrence E8ComposeCoeff7

private theorem powCoeff_two_four (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 2 4 = 2 * b 1 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, powCoeff_one]
  ring

private theorem powCoeff_three_five (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 3 5 = 3 * b 1 ^ 2 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, powCoeff_two_four,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

private theorem powCoeff_four_six (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 4 6 = 4 * b 1 ^ 3 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, powCoeff_three_five,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

private theorem powCoeff_five_seven (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 5 7 = 5 * b 1 ^ 4 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, powCoeff_four_six,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

private theorem powCoeff_six_eight (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 6 8 = 6 * b 1 ^ 5 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, powCoeff_five_seven,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

private theorem powCoeff_seven_nine (b : ℕ → ℂ) (b0 : b 0 = 0) (b2 : b 2 = 0) :
    powCoeff b 7 9 = 7 * b 1 ^ 6 * b 3 := by
  rw [powCoeff]
  simp [Finset.sum_range_succ, b0, b2, powCoeff_six_eight,
    powCoeff_zero_of_lt, powCoeff_diag]
  ring

private theorem powCoeff_three_nine_odd (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) :
    powCoeff b 3 9 = 3*b 1^2*b 7 + 6*b 1*b 3*b 5 + b 3^3 := by
  simp (config := { maxSteps := 1000000 })
    [powCoeff, Finset.sum_range_succ, b0, b2, b4, b6, b8]
  ring

set_option maxHeartbeats 0 in
private theorem powCoeff_five_nine_odd (b : ℕ → ℂ)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) :
    powCoeff b 5 9 = 5*b 1^4*b 5 + 10*b 1^3*b 3^2 := by
  simp (config := { maxSteps := 1000000 })
    [powCoeff, Finset.sum_range_succ, b0, b2, b4, b6, b8]
  ring

theorem composeCoeff_nine_odd (a b : ℕ → ℂ)
    (a2 : a 2 = 0) (a4 : a 4 = 0) (a6 : a 6 = 0)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0)
    (b6 : b 6 = 0) (b8 : b 8 = 0) :
    composeCoeff a b 9 = a 1*b 9 +
      a 3*(3*b 1^2*b 7 + 6*b 1*b 3*b 5 + b 3^3) +
      a 5*(5*b 1^4*b 5 + 10*b 1^3*b 3^2) +
      a 7*(7*b 1^6*b 3) + a 9*b 1^9 := by
  simp only [composeCoeff, Finset.sum_range_succ]
  rw [a2, a4, a6]
  simp only [zero_mul, add_zero]
  rw [powCoeff_one,
    powCoeff_three_nine_odd b b0 b2 b4 b6 b8,
    powCoeff_five_nine_odd b b0 b2 b4 b6 b8,
    powCoeff_seven_nine b b0 b2,
    powCoeff_next_diag_zero b b0 b2 8,
    powCoeff_diag b b0 9]
  simp [powCoeff, b0]

end GeneralCK.Certificates.E8ComposeCoeff9

end


