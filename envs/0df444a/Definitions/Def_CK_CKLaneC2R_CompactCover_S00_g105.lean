-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g105
-- name    : CK_CKLaneC2R_CompactCover_S00_g105
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T20:28:16.231993+00:00
-- url     : https://prove2.me/theorems/d1eb8557-c8ca-439c-9217-ffd77979d3d1
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

import Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g105_q00

namespace CKLaneC2R.CompactCover
theorem strip0_s133 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : ¬ (a ≤ ((31/160 : ℚ) : ℝ))) (h1381 : z ≤ ((217/400 : ℚ) : ℝ)) (h1382 : ¬ (a ≤ ((63/320 : ℚ) : ℝ))) (h1417 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1441 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h1442 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1443 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1444 : z ≤ ((841/2560 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B015.c307_pos (not_le.mp h1382).le ha2 (not_le.mp h1417).le h1444
        · -- right
          exact CKLaneC2R.Cells.S00.B015.c308_pos (not_le.mp h1382).le ha2 (not_le.mp h1444).le h1443
      · -- right
        by_cases h1445 : z ≤ ((22851/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B015.c311_pos (not_le.mp h1382).le ha2 (not_le.mp h1443).le h1445
        · -- right
          exact CKLaneC2R.Cells.S00.B015.c312_pos (not_le.mp h1382).le ha2 (not_le.mp h1445).le h1442
    · -- right
      by_cases h1446 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B000.c1_pos (not_le.mp h1382).le ha2 (not_le.mp h1442).le h1446
      · -- right
        exact CKLaneC2R.Cells.S00.B000.c3_pos (not_le.mp h1382).le ha2 (not_le.mp h1446).le h1441
  · -- right
    by_cases h1447 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1448 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B000.c13_pos (not_le.mp h1382).le ha2 (not_le.mp h1441).le h1448
      · -- right
        exact CKLaneC2R.Cells.S00.B000.c15_pos (not_le.mp h1382).le ha2 (not_le.mp h1448).le h1447
    · -- right
      by_cases h1449 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B001.c21_pos (not_le.mp h1382).le ha2 (not_le.mp h1447).le h1449
      · -- right
        exact CKLaneC2R.Cells.S00.B001.c23_pos (not_le.mp h1382).le ha2 (not_le.mp h1449).le h1381

end CKLaneC2R.CompactCover


