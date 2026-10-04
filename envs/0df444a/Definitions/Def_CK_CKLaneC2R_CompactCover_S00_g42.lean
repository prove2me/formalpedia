-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g42
-- name    : CK_CKLaneC2R_CompactCover_S00_g42
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T12:08:05.898913+00:00
-- url     : https://prove2.me/theorems/eaded887-812b-411b-83d5-562257497b89
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B007
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B009

namespace CKLaneC2R.CompactCover

theorem strip0_s049 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : a ≤ ((27/160 : ℚ) : ℝ)) (h482 : a ≤ ((53/320 : ℚ) : ℝ)) (h483 : z ≤ ((217/400 : ℚ) : ℝ)) (h484 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h527 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h528 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h529 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h530 : z ≤ ((841/2560 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B006.c135_pos (not_le.mp h1).le h482 (not_le.mp h484).le h530
        · -- right
          exact CKLaneC2R.Cells.S00.B006.c136_pos (not_le.mp h1).le h482 (not_le.mp h530).le h529
      · -- right
        by_cases h531 : z ≤ ((22851/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B006.c139_pos (not_le.mp h1).le h482 (not_le.mp h529).le h531
        · -- right
          exact CKLaneC2R.Cells.S00.B007.c140_pos (not_le.mp h1).le h482 (not_le.mp h531).le h528
    · -- right
      by_cases h532 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        by_cases h533 : z ≤ ((24677/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B007.c151_pos (not_le.mp h1).le h482 (not_le.mp h528).le h533
        · -- right
          exact CKLaneC2R.Cells.S00.B007.c152_pos (not_le.mp h1).le h482 (not_le.mp h533).le h532
      · -- right
        by_cases h534 : z ≤ ((26503/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B007.c155_pos (not_le.mp h1).le h482 (not_le.mp h532).le h534
        · -- right
          exact CKLaneC2R.Cells.S00.B007.c156_pos (not_le.mp h1).le h482 (not_le.mp h534).le h527
  · -- right
    by_cases h535 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h536 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        by_cases h537 : z ≤ ((28329/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B008.c167_pos (not_le.mp h1).le h482 (not_le.mp h527).le h537
        · -- right
          exact CKLaneC2R.Cells.S00.B008.c168_pos (not_le.mp h1).le h482 (not_le.mp h537).le h536
      · -- right
        by_cases h538 : z ≤ ((6031/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B008.c171_pos (not_le.mp h1).le h482 (not_le.mp h536).le h538
        · -- right
          exact CKLaneC2R.Cells.S00.B008.c172_pos (not_le.mp h1).le h482 (not_le.mp h538).le h535
    · -- right
      by_cases h539 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        by_cases h540 : z ≤ ((31981/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B009.c183_pos (not_le.mp h1).le h482 (not_le.mp h535).le h540
        · -- right
          exact CKLaneC2R.Cells.S00.B009.c184_pos (not_le.mp h1).le h482 (not_le.mp h540).le h539
      · -- right
        by_cases h541 : z ≤ ((33807/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B009.c187_pos (not_le.mp h1).le h482 (not_le.mp h539).le h541
        · -- right
          exact CKLaneC2R.Cells.S00.B009.c188_pos (not_le.mp h1).le h482 (not_le.mp h541).le h483

end CKLaneC2R.CompactCover


