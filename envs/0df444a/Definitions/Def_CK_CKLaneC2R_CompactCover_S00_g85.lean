-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g85
-- name    : CK_CKLaneC2R_CompactCover_S00_g85
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T13:24:22.07546+00:00
-- url     : https://prove2.me/theorems/5b4158c5-ab25-4fd6-8420-b6bea2f011a9
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S00 (proof part of strip0) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S00 (proof part of strip0).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B010
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B011

namespace CKLaneC2R.CompactCover

theorem strip0_s105 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : ¬ (a ≤ ((29/160 : ℚ) : ℝ))) (h1078 : z ≤ ((217/400 : ℚ) : ℝ)) (h1079 : ¬ (a ≤ ((59/320 : ℚ) : ℝ))) (h1124 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1125 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1145 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h1146 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1147 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B010.c211_pos (not_le.mp h1079).le h891 (not_le.mp h1125).le h1147
      · -- right
        exact CKLaneC2R.Cells.S00.B010.c212_pos (not_le.mp h1079).le h891 (not_le.mp h1147).le h1146
    · -- right
      by_cases h1148 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B010.c215_pos (not_le.mp h1079).le h891 (not_le.mp h1146).le h1148
      · -- right
        exact CKLaneC2R.Cells.S00.B010.c216_pos (not_le.mp h1079).le h891 (not_le.mp h1148).le h1145
  · -- right
    by_cases h1149 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1150 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B011.c227_pos (not_le.mp h1079).le h891 (not_le.mp h1145).le h1150
      · -- right
        exact CKLaneC2R.Cells.S00.B011.c228_pos (not_le.mp h1079).le h891 (not_le.mp h1150).le h1149
    · -- right
      by_cases h1151 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B011.c231_pos (not_le.mp h1079).le h891 (not_le.mp h1149).le h1151
      · -- right
        exact CKLaneC2R.Cells.S00.B011.c232_pos (not_le.mp h1079).le h891 (not_le.mp h1151).le h1124

end CKLaneC2R.CompactCover


