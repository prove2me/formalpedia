-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g04
-- name    : CK_CKLaneC2R_CompactCover_S01_g04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T19:30:50.890315+00:00
-- url     : https://prove2.me/theorems/6592ceae-c314-4c77-a554-632bc1638136
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S01 (proof part of strip1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S01 (proof part of strip1).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B033
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B034

namespace CKLaneC2R.CompactCover

theorem strip1_s004 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : a ≤ ((33/160 : ℚ) : ℝ)) (h4 : z ≤ ((217/400 : ℚ) : ℝ)) (h5 : ¬ (a ≤ ((13/64 : ℚ) : ℝ))) (h36 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h37 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h51 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h52 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h53 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B033.c664_pos (not_le.mp h5).le h3 (not_le.mp h37).le h53
      · -- right
        exact CKLaneC2R.Cells.S01.B033.c666_pos (not_le.mp h5).le h3 (not_le.mp h53).le h52
    · -- right
      by_cases h54 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B033.c669_pos (not_le.mp h5).le h3 (not_le.mp h52).le h54
      · -- right
        exact CKLaneC2R.Cells.S01.B033.c670_pos (not_le.mp h5).le h3 (not_le.mp h54).le h51
  · -- right
    by_cases h55 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h56 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B034.c681_pos (not_le.mp h5).le h3 (not_le.mp h51).le h56
      · -- right
        exact CKLaneC2R.Cells.S01.B034.c682_pos (not_le.mp h5).le h3 (not_le.mp h56).le h55
    · -- right
      by_cases h57 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B034.c685_pos (not_le.mp h5).le h3 (not_le.mp h55).le h57
      · -- right
        exact CKLaneC2R.Cells.S01.B034.c686_pos (not_le.mp h5).le h3 (not_le.mp h57).le h36

end CKLaneC2R.CompactCover


