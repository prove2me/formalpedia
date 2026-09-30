-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailFifteenthThirtySecondsIdentity
-- name    : CK_GeneralCK_PureGapDoubleCapHighTailFifteenthThirtySecondsIdentity
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:09:10.943505+00:00
-- url     : https://prove2.me/theorems/3de6acf1-def2-4d17-8ac5-eaabcdf76153
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsIdentity` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsIdentity` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsIdentity` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsIdentity (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapHighTailFifteenthThirtySecondsIdentity.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailIdentity

-- ===== source module GeneralCK.PureGapDoubleCapHighTailFifteenthThirtySecondsIdentity =====
section

/-! Wider exact inverse-entropy square enclosure on x≤1/16. Draft until Lean audit. -/

namespace GeneralCK

theorem doubleCapHighTailFifteenthY_sq_le {x : ℝ}
    (hx : 0 < x) (hx16 : x ≤ 1 / 16) :
    0 ≤ doubleCapHighTailY x ∧
    doubleCapHighTailY x ^ 2 ≤ (128 / 63 : ℝ) * x ^ 2 ∧
    doubleCapHighTailY x ^ 2 ≤ 1 / 126 := by
  have hx1 : x < 1 / 2 := by linarith
  have hh := doubleCapHighTailFloor_pos hx hx1
  have hh1 := doubleCapHighTailFloor_le_one hx hx1
  have hy0 : 0 ≤ doubleCapHighTailY x := by
    unfold doubleCapHighTailY
    linarith [(entropyInverse_spec hh.le hh1).2.1]
  have hy1 : doubleCapHighTailY x < 1 := by
    unfold doubleCapHighTailY
    linarith [entropyInverse_pos hh hh1]
  have hY := SmallMean.Cn_ge_half_sq hy0 hy1.le
  have hX := SmallMean.Cn_le_half_sq_over_gap
    (show 0 ≤ 2 * x by positivity) (show 2 * x < 1 by linarith)
  have hEq := doubleCapHighTailY_deficit hx hx1
  have hu : x ^ 2 ≤ 1 / 256 := by
    have hsq := (sq_le_sq₀ hx.le
      (by norm_num : (0 : ℝ) ≤ 1 / 16)).2 hx16
    norm_num at hsq
    exact hsq
  have hgap : 0 < 1 - 4 * x ^ 2 := by nlinarith [hu]
  have hgap2 : 0 < 1 - (2 * x) ^ 2 := by nlinarith [hgap]
  have hYraw : doubleCapHighTailY x ^ 2 / 2 ≤
      x ^ 2 / (1 - 4 * x ^ 2) := by
    have hX2 : SmallMean.Cn (2 * x) / 2 ≤
        (2 * x) ^ 2 / (4 * (1 - (2 * x) ^ 2)) := by
      calc
        _ ≤ ((2 * x) ^ 2 / (2 * (1 - (2 * x) ^ 2))) / 2 :=
          div_le_div_of_nonneg_right hX (by norm_num : (0 : ℝ) ≤ 2)
        _ = (2 * x) ^ 2 / (4 * (1 - (2 * x) ^ 2)) := by
          field_simp [hgap2.ne']
          ring
    calc
      _ ≤ SmallMean.Cn (doubleCapHighTailY x) := hY
      _ = SmallMean.Cn (2 * x) / 2 := hEq
      _ ≤ (2 * x) ^ 2 / (4 * (1 - (2 * x) ^ 2)) := hX2
      _ = x ^ 2 / (1 - 4 * x ^ 2) := by
        field_simp [hgap.ne']
        ring
  have hgapLo : (63 / 64 : ℝ) ≤ 1 - 4 * x ^ 2 := by nlinarith [hu]
  have hraw : doubleCapHighTailY x ^ 2 ≤
      2 * x ^ 2 / (1 - 4 * x ^ 2) := by
    have heq : 2 * (x ^ 2 / (1 - 4 * x ^ 2)) =
        2 * x ^ 2 / (1 - 4 * x ^ 2) := by ring
    rw [← heq]
    linarith [hYraw]
  have hrat : 2 * x ^ 2 / (1 - 4 * x ^ 2) ≤
      (128 / 63 : ℝ) * x ^ 2 := by
    apply (div_le_iff₀ hgap).2
    have hm := mul_le_mul_of_nonneg_left hgapLo
      (show 0 ≤ (128 / 63 : ℝ) * x ^ 2 by positivity)
    nlinarith [hm]
  have hsq : doubleCapHighTailY x ^ 2 ≤
      (128 / 63 : ℝ) * x ^ 2 := hraw.trans hrat
  refine ⟨hy0, hsq, ?_⟩
  nlinarith [hsq, hu]

#print axioms doubleCapHighTailFifteenthY_sq_le

end GeneralCK

end


