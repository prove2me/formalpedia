-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g08
-- name    : CK_CKLaneC2R_CompactCover_S03_g08
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T17:41:46.916157+00:00
-- url     : https://prove2.me/theorems/3bc7c9f2-339e-4ebc-a877-6507b8231da9
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S03 (proof part of strip3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S03 (proof part of strip3).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S03_B007
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B012

namespace CKLaneC2R.CompactCover

theorem strip3_s013 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((3/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((11/20 : ℚ) : ℝ))) (h119 : a ≤ ((23/40 : ℚ) : ℝ)) (h120 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h145 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h153 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h154 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h155 : a ≤ ((9/16 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S03.B007.c149_pos (not_le.mp h1).le h155 (not_le.mp h145).le h154
    · -- right
      exact CKLaneC2R.Cells.S03.B007.c150_pos (not_le.mp h155).le h119 (not_le.mp h145).le h154
  · -- right
    by_cases h156 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S03.B007.c153_pos (not_le.mp h1).le h119 (not_le.mp h154).le h156
    · -- right
      by_cases h157 : a ≤ ((9/16 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B012.c256_pos (not_le.mp h1).le h157 (not_le.mp h156).le h153
      · -- right
        exact CKLaneC2R.Cells.S03.B012.c257_pos (not_le.mp h157).le h119 (not_le.mp h156).le h153

end CKLaneC2R.CompactCover


