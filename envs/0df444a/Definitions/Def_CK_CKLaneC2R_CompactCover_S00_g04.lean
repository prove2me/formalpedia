-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g04
-- name    : CK_CKLaneC2R_CompactCover_S00_g04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T01:45:42.941918+00:00
-- url     : https://prove2.me/theorems/64b0073c-f70b-4f05-bf89-cd4623c98420
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B035
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B036
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B037

namespace CKLaneC2R.CompactCover

theorem strip0_s005 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : a ≤ ((49/320 : ℚ) : ℝ)) (h4 : z ≤ ((217/400 : ℚ) : ℝ)) (h5 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h6 : ¬ (a ≤ ((97/640 : ℚ) : ℝ))) (h32 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h50 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h51 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h52 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B035.c710_pos (not_le.mp h6).le h3 (not_le.mp h32).le h52
      · -- right
        exact CKLaneC2R.Cells.S00.B035.c712_pos (not_le.mp h6).le h3 (not_le.mp h52).le h51
    · -- right
      by_cases h53 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B035.c718_pos (not_le.mp h6).le h3 (not_le.mp h51).le h53
      · -- right
        exact CKLaneC2R.Cells.S00.B036.c720_pos (not_le.mp h6).le h3 (not_le.mp h53).le h50
  · -- right
    by_cases h54 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h55 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B037.c742_pos (not_le.mp h6).le h3 (not_le.mp h50).le h55
      · -- right
        exact CKLaneC2R.Cells.S00.B037.c744_pos (not_le.mp h6).le h3 (not_le.mp h55).le h54
    · -- right
      by_cases h56 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B037.c750_pos (not_le.mp h6).le h3 (not_le.mp h54).le h56
      · -- right
        exact CKLaneC2R.Cells.S00.B037.c752_pos (not_le.mp h6).le h3 (not_le.mp h56).le h5

end CKLaneC2R.CompactCover


