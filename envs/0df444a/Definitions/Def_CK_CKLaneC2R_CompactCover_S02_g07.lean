-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g07
-- name    : CK_CKLaneC2R_CompactCover_S02_g07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T12:07:58.263809+00:00
-- url     : https://prove2.me/theorems/ce8ab05a-f3c3-4ed0-b1ca-ed34cf0e0b02
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S02 (proof part of strip2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S02 (proof part of strip2).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B017

namespace CKLaneC2R.CompactCover

theorem strip2_s009 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : a ≤ ((13/40 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((5/16 : ℚ) : ℝ))) (h93 : z ≤ ((217/400 : ℚ) : ℝ)) (h94 : a ≤ ((51/160 : ℚ) : ℝ)) (h95 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h110 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h111 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h112 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B016.c324_pos (not_le.mp h3).le h94 (not_le.mp h95).le h112
      · -- right
        exact CKLaneC2R.Cells.S02.B016.c326_pos (not_le.mp h3).le h94 (not_le.mp h112).le h111
    · -- right
      by_cases h113 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B016.c332_pos (not_le.mp h3).le h94 (not_le.mp h111).le h113
      · -- right
        exact CKLaneC2R.Cells.S02.B016.c334_pos (not_le.mp h3).le h94 (not_le.mp h113).le h110
  · -- right
    by_cases h114 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h115 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B017.c340_pos (not_le.mp h3).le h94 (not_le.mp h110).le h115
      · -- right
        exact CKLaneC2R.Cells.S02.B017.c342_pos (not_le.mp h3).le h94 (not_le.mp h115).le h114
    · -- right
      by_cases h116 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B017.c348_pos (not_le.mp h3).le h94 (not_le.mp h114).le h116
      · -- right
        exact CKLaneC2R.Cells.S02.B017.c350_pos (not_le.mp h3).le h94 (not_le.mp h116).le h93

end CKLaneC2R.CompactCover


