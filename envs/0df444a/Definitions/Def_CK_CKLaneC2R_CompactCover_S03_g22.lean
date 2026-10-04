-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g22
-- name    : CK_CKLaneC2R_CompactCover_S03_g22
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T08:26:47.34111+00:00
-- url     : https://prove2.me/theorems/95d1495d-8909-4b3d-b8d2-e8d4e414cde9
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

import Definitions.Def_CK_CKLaneC2R_Cells_S03_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B011
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B012
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B001
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B002

namespace CKLaneC2R.CompactCover

theorem strip3_s031 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((3/5 : ℚ) : ℝ))) (h220 : ¬ (a ≤ ((13/20 : ℚ) : ℝ))) (h313 : ¬ (a ≤ ((27/40 : ℚ) : ℝ))) (h357 : z ≤ ((217/400 : ℚ) : ℝ)) (h358 : z ≤ ((1257/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h359 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h360 : z ≤ ((2289/16000 : ℚ) : ℝ)
    · -- left
      by_cases h361 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h362 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          by_cases h363 : a ≤ ((11/16 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B016.c336_pos (not_le.mp h313).le h363 hz1 h362
          · -- right
            exact CKLaneC2R.Cells.S03.B016.c337_pos (not_le.mp h363).le ha2 hz1 h362
        · -- right
          exact CKLaneC2R.Cells.S03.B011.c235_pos (not_le.mp h313).le ha2 (not_le.mp h362).le h361
      · -- right
        by_cases h364 : a ≤ ((11/16 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B011.c236_pos (not_le.mp h313).le h364 (not_le.mp h361).le h360
        · -- right
          exact CKLaneC2R.Cells.S03.B011.c237_pos (not_le.mp h364).le ha2 (not_le.mp h361).le h360
    · -- right
      by_cases h365 : z ≤ ((5491/32000 : ℚ) : ℝ)
      · -- left
        by_cases h366 : a ≤ ((11/16 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B012.c240_pos (not_le.mp h313).le h366 (not_le.mp h360).le h365
        · -- right
          exact CKLaneC2R.Cells.S03.B012.c241_pos (not_le.mp h366).le ha2 (not_le.mp h360).le h365
      · -- right
        exact CKLaneC2R.Cells.S03.B001.c35_pos (not_le.mp h313).le ha2 (not_le.mp h365).le h359
  · -- right
    by_cases h367 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h368 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B002.c45_pos (not_le.mp h313).le ha2 (not_le.mp h359).le h368
      · -- right
        exact CKLaneC2R.Cells.S03.B002.c46_pos (not_le.mp h313).le ha2 (not_le.mp h368).le h367
    · -- right
      by_cases h369 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B002.c49_pos (not_le.mp h313).le ha2 (not_le.mp h367).le h369
      · -- right
        exact CKLaneC2R.Cells.S03.B002.c50_pos (not_le.mp h313).le ha2 (not_le.mp h369).le h358

end CKLaneC2R.CompactCover


