-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailRational
-- name    : CK_GeneralCK_PureGapDoubleCapHighTailRational
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:53:30.46904+00:00
-- url     : https://prove2.me/theorems/1cf0881d-d6b6-4d35-9ec3-e21480283408
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapHighTailRational` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapHighTailRational` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapHighTailRational` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapHighTailRational (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapHighTailRational.lean)

import Definitions.Def_CK_GeneralCK_SmallMeanCapTailBounds

-- ===== source module GeneralCK.PureGapDoubleCapHighTailRational =====
section

/-! Small rational inequality isolated from the high double-cap logarithm
and implicit-contact proofs. -/

namespace GeneralCK

theorem doubleCapHighTail_negative_rational_bound {u t : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 1024)
    (ht0 : 0 ≤ t) (htu : t ≤ (512 / 255 : ℝ) * u) :
    -(10455040 / 3893697 : ℝ) * u ≤
      2 - 2 / ((1 - t) * (1 + t / 3)) := by
  have htlim : t ≤ 1 / 510 := by nlinarith [htu, hu1]
  have htsq : t ^ 2 ≤ t / 510 := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr htlim)]
  let D : ℝ := (1 - t) * (1 + t / 3)
  have hD : (499 / 500 : ℝ) ≤ D := by
    dsimp [D]
    nlinarith [htlim, htsq]
  have hDpos : 0 < D := (by norm_num : (0 : ℝ) < 499 / 500).trans_le hD
  have hnum : 0 ≤ 2 * t + t ^ 2 := by positivity
  have hnumLe : 2 * t + t ^ 2 ≤ (1021 / 510 : ℝ) * t := by
    nlinarith [htsq]
  have hcross :
      (2 * t + t ^ 2) * (499 / 500 : ℝ) ≤
        ((1021 / 510 : ℝ) * t) * D := by
    have h1 := mul_le_mul_of_nonneg_right hnumLe
      (by norm_num : (0 : ℝ) ≤ 499 / 500)
    have h2 := mul_le_mul_of_nonneg_left hD
      (show 0 ≤ (1021 / 510 : ℝ) * t by positivity)
    nlinarith [h1, h2]
  have hquot : (2 * t + t ^ 2) / D ≤
      ((1021 / 510 : ℝ) * t) / (499 / 500 : ℝ) := by
    apply (div_le_div_iff₀ hDpos
      (by norm_num : (0 : ℝ) < 499 / 500)).2
    exact hcross
  have hratio : (2 / 3 : ℝ) *
      (((1021 / 510 : ℝ) * t) / (499 / 500 : ℝ)) ≤
      (10455040 / 3893697 : ℝ) * u := by
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

theorem doubleCapHighTail_rational_margin_pos :
    0 < (10240 / 3589 : ℝ) - (10455040 / 3893697 : ℝ) := by
  norm_num

#print axioms doubleCapHighTail_negative_rational_bound
#print axioms doubleCapHighTail_rational_margin_pos

end GeneralCK

end


