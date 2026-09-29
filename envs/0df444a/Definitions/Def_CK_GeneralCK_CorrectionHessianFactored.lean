-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionHessianFactored
-- name    : CK_GeneralCK_CorrectionHessianFactored
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:43:50.461676+00:00
-- url     : https://prove2.me/theorems/08beece9-c48b-4eed-b1d3-5898b1c7a4fb
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionHessianFactored` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionHessianFactored` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionHessianFactored` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionHessianFactored (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionHessianFactored.lean)

import Definitions.Def_CK_GeneralCK_CorrectionHessianPSD
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2

namespace GeneralCK.Correction




















theorem Mdet_rank_one (e f : ℝ) :
    Mdet e f = Aleft e f * Aright e f - (q e + q f)^2 -
      rankWeight e f * (Aleft e f * (Zright e f)^2 +
        Aright e f * (Zleft e f)^2 +
        2 * (q e + q f) * Zleft e f * Zright e f) := by
  unfold Mdet Mleft Mright Mcross rankWeight
  ring

theorem naturalJ_pos {f : ℝ} (hf : 0 < f) (hf' : f < 1) :
    0 < naturalJ f :=
  mul_pos log_two_pos (J_pos (entropyInverse_pos hf hf'.le)
    (entropyInverse_lt_half hf.le hf'))

theorem Aright_eq_numerator (e f : ℝ) :
    Aright e f = rightNumerator e f / naturalJ f := rfl

theorem naturalJ_mul_Aright {e f : ℝ} (hJ : naturalJ f ≠ 0) :
    naturalJ f * Aright e f = rightNumerator e f := by
  rw [Aright_eq_numerator]
  exact mul_div_cancel₀ _ hJ

/-- The nonzero slope hypothesis is essential when clearing the right denominator. -/
theorem Kfactored_eq_mul_Mdet {e f : ℝ} (hJ : naturalJ f ≠ 0) :
    Kfactored e f = naturalJ f * Mdet e f := by
  rw [Mdet_rank_one]
  unfold Kfactored
  linear_combination
    (rankWeight e f * (Zleft e f)^2 - Aleft e f) *
      (naturalJ_mul_Aright (e := e) hJ)

theorem Kfactored_eq_mul_Mdet_interior {e f : ℝ} (hf : 0 < f) (hf' : f < 1) :
    Kfactored e f = naturalJ f * Mdet e f :=
  Kfactored_eq_mul_Mdet (naturalJ_pos hf hf').ne'

theorem Mdet_pos_iff_Kfactored_pos {e f : ℝ} (hf : 0 < f) (hf' : f < 1) :
    0 < Mdet e f ↔ 0 < Kfactored e f := by
  rw [Kfactored_eq_mul_Mdet_interior hf hf']
  exact (mul_pos_iff_of_pos_left (naturalJ_pos hf hf')).symm

theorem Mdet_nonneg_iff_Kfactored_nonneg {e f : ℝ} (hf : 0 < f) (hf' : f < 1) :
    0 ≤ Mdet e f ↔ 0 ≤ Kfactored e f := by
  rw [Kfactored_eq_mul_Mdet_interior hf hf']
  exact (mul_nonneg_iff_of_pos_left (naturalJ_pos hf hf')).symm

end GeneralCK.Correction


