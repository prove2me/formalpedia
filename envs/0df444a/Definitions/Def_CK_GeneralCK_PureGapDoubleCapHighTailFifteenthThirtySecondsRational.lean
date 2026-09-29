-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailFifteenthThirtySecondsRational
-- name    : CK_GeneralCK_PureGapDoubleCapHighTailFifteenthThirtySecondsRational
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:00:17.640428+00:00
-- url     : https://prove2.me/theorems/02afa887-2544-4231-a119-961b7083960b
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsRational` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsRational` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsRational` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsRational (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapHighTailFifteenthThirtySecondsRational.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailRational

-- ===== source module GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsRational =====
section

/-! Exact rational checker for the proposed wider `x≤1/16` high tail.
This source is a draft until a named Lean audit passes. -/

namespace GeneralCK

theorem doubleCapHighTailFifteenth_negative_rational_bound {u t : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 256)
    (ht0 : 0 ≤ t) (htu : t ≤ (128 / 63 : ℝ) * u) :
    -(129536 / 47375 : ℝ) * u ≤
      2 - 2 / ((1 - t) * (1 + t / 3)) := by
  have htlim : t ≤ 1 / 126 := by nlinarith [htu, hu1]
  have htsq : t ^ 2 ≤ t / 126 := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr htlim)]
  let D : ℝ := (1 - t) * (1 + t / 3)
  have hD : (47375 / 47628 : ℝ) ≤ D := by
    dsimp [D]
    nlinarith [htlim, htsq]
  have hDpos : 0 < D := (by norm_num : (0 : ℝ) < 47375 / 47628).trans_le hD
  have hnum : 0 ≤ 2 * t + t ^ 2 := by positivity
  have hnumLe : 2 * t + t ^ 2 ≤ (253 / 126 : ℝ) * t := by
    nlinarith [htsq]
  have hcross :
      (2 * t + t ^ 2) * (47375 / 47628 : ℝ) ≤
      ((253 / 126 : ℝ) * t) * D := by
    have h1 := mul_le_mul_of_nonneg_right hnumLe
      (by norm_num : (0 : ℝ) ≤ 47375 / 47628)
    have h2 := mul_le_mul_of_nonneg_left hD
      (show 0 ≤ (253 / 126 : ℝ) * t by positivity)
    nlinarith [h1, h2]
  have hquot : (2 * t + t ^ 2) / D ≤
      ((253 / 126 : ℝ) * t) / (47375 / 47628 : ℝ) := by
    apply (div_le_div_iff₀ hDpos
      (by norm_num : (0 : ℝ) < 47375 / 47628)).2
    exact hcross
  have hratio : (2 / 3 : ℝ) *
      (((253 / 126 : ℝ) * t) / (47375 / 47628 : ℝ)) ≤
      (129536 / 47375 : ℝ) * u := by
    nlinarith [htu]
  have htOne : 0 < 1 - t := by linarith [htlim]
  have htPlus : 0 < 1 + t / 3 := by linarith [ht0]
  have heq : 2 - 2 / D = -(2 / 3 : ℝ) *
      ((2 * t + t ^ 2) / D) := by
    dsimp [D]
    field_simp [htOne.ne', htPlus.ne', hDpos.ne']
    ring
  rw [show (1 - t) * (1 + t / 3) = D by rfl, heq]
  nlinarith [hquot, hratio]

theorem doubleCapHighTailFifteenth_positive_rational_bound {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 256) :
    (2560 / 901 : ℝ) * u ≤
      2 * u / ((1 - u) * (7 / 10 + u)) := by
  have hgap : 0 < 1 - u := by linarith
  have hB : 0 < (7 / 10 : ℝ) + u := by linarith
  have hden : 0 < (1 - u) * (7 / 10 + u) := mul_pos hgap hB
  have hBhi : (7 / 10 : ℝ) + u ≤ 901 / 1280 := by linarith [hu1]
  have hdenHi : (1 - u) * (7 / 10 + u) ≤ 901 / 1280 := by
    have hm := mul_le_mul_of_nonneg_right
      (show 1 - u ≤ (1 : ℝ) by linarith) hB.le
    nlinarith [hm, hBhi]
  apply (le_div_iff₀ hden).2
  have hm := mul_le_mul_of_nonneg_left hdenHi hu0
  nlinarith [hm]

theorem doubleCapHighTailFifteenth_margin_pos :
    0 < (2560 / 901 : ℝ) - (129536 / 47375 : ℝ) := by
  norm_num

#print axioms doubleCapHighTailFifteenth_negative_rational_bound
#print axioms doubleCapHighTailFifteenth_positive_rational_bound
#print axioms doubleCapHighTailFifteenth_margin_pos

end GeneralCK

end


