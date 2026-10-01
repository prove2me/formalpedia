-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailUniformSecantAlgebra
-- name    : CK_GeneralCK_PureGapDoubleCapLowTailUniformSecantAlgebra
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T11:18:55.500975+00:00
-- url     : https://prove2.me/theorems/6b4f4ce2-f56b-432c-9132-f04d8ed092ad
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapLowTailUniformSecantAlgebra` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapLowTailUniformSecantAlgebra` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapLowTailUniformSecantAlgebra` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapLowTailUniformSecantAlgebra (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapLowTailUniformSecantAlgebra.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailDiagonalQuantitative

-- ===== source module GeneralCK.PureGapDoubleCapLowTailUniformSecantAlgebra =====
section

/-! Exact rational algebra behind the uniform near-zero contact-loss
estimate. The analytic and contact hypotheses will be discharged separately. -/

namespace GeneralCK

theorem doubleCapLowTail_uniform_secant_abstract
    {m d k bc bY p q δ den : ℝ}
    (hm : 0 < m) (hd : 0 < d) (hmd : m ≤ d)
    (hk : 49 / 50 ≤ k) (hbc : 207 / 100 ≤ bc)
    (hp : 99 / 50 ≤ p) (hq : 99 / 50 ≤ q)
    (hby : 0 < bY) (hden : 0 < den)
    (hδ : 0 ≤ δ)
    (hsep : δ * k ^ 2 * bc ≤ (5 / 2) * m * d * bY)
    (hDenLower : d ^ 2 * p * q * bY ≤ den) :
    4 * δ / den ≤ 4 / 3 := by
  have hk0 : 0 < k := by linarith
  have hbc0 : 0 < bc := by linarith
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hKbc : 0 < k ^ 2 * bc := mul_pos (sq_pos_of_pos hk0) hbc0
  have hKsq : (49 / 50 : ℝ) ^ 2 ≤ k ^ 2 := by nlinarith [hk]
  have hKB : (49 / 50 : ℝ) ^ 2 * (207 / 100) ≤ k ^ 2 * bc :=
    (mul_le_mul_of_nonneg_left hbc (by norm_num :
      (0 : ℝ) ≤ (49 / 50) ^ 2)).trans
      (mul_le_mul_of_nonneg_right hKsq hbc0.le)
  have hPQ : (99 / 50 : ℝ) ^ 2 ≤ p * q := by
    have h1 := mul_le_mul_of_nonneg_left hq
      (by norm_num : (0 : ℝ) ≤ 99 / 50)
    have h2 := mul_le_mul_of_nonneg_right hp hq0.le
    nlinarith only [h1, h2]
  have hProd : (15 / 2 : ℝ) ≤ (k ^ 2 * bc) * (p * q) := by
    have hConst : (15 / 2 : ℝ) ≤
        ((49 / 50 : ℝ) ^ 2 * (207 / 100)) * ((99 / 50 : ℝ) ^ 2) := by
      norm_num
    have h1 := mul_le_mul_of_nonneg_left hPQ
      (by norm_num : (0 : ℝ) ≤ (49 / 50) ^ 2 * (207 / 100))
    have h2 := mul_le_mul_of_nonneg_right hKB
      (mul_nonneg hp0.le hq0.le)
    nlinarith only [hConst, h1, h2]
  have hTen : 10 * m ≤ (4 / 3) * (k ^ 2 * bc) * (p * q) * d := by
    have h1 := mul_le_mul_of_nonneg_left hmd
      (by norm_num : (0 : ℝ) ≤ 10)
    have h2 := mul_le_mul_of_nonneg_right hProd
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3) hd.le)
    nlinarith only [h1, h2]
  have hTenScaled : 10 * m * d * bY ≤
      (4 / 3) * (k ^ 2 * bc) * (d ^ 2 * p * q * bY) := by
    have h := mul_le_mul_of_nonneg_right hTen
      (mul_nonneg hd.le hby.le)
    nlinarith only [h]
  have hDenScaled : (4 / 3) * (k ^ 2 * bc) *
      (d ^ 2 * p * q * bY) ≤ (4 / 3) * (k ^ 2 * bc) * den :=
    mul_le_mul_of_nonneg_left hDenLower
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3) hKbc.le)
  have hSepScaled : 4 * δ * (k ^ 2 * bc) ≤ 10 * m * d * bY := by
    nlinarith [hsep]
  have hCross : 4 * δ * (k ^ 2 * bc) ≤
      (4 / 3) * (k ^ 2 * bc) * den :=
    (hSepScaled.trans hTenScaled).trans hDenScaled
  have hNumerator : 4 * δ ≤ (4 / 3) * den := by
    by_contra h
    have hStrict : (4 / 3) * den < 4 * δ := lt_of_not_ge h
    have hStrictMul := mul_lt_mul_of_pos_right hStrict hKbc
    nlinarith only [hCross, hStrictMul]
  exact (div_le_iff₀ hden).mpr hNumerator

#print axioms doubleCapLowTail_uniform_secant_abstract

end GeneralCK

end


