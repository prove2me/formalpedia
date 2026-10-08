-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g34
-- name    : CK_CKLaneC2R_CompactCover_S02_g34
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T12:11:48.403704+00:00
-- url     : https://prove2.me/theorems/5e49227d-542d-4568-8926-09182dfb6a5e
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B033
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B034
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B021
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B003

namespace CKLaneC2R.CompactCover

theorem strip2_s052 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : a ≤ ((9/20 : ℚ) : ℝ)) (h535 : a ≤ ((17/40 : ℚ) : ℝ)) (h536 : a ≤ ((33/80 : ℚ) : ℝ)) (h537 : z ≤ ((217/400 : ℚ) : ℝ)) (h538 : z ≤ ((1257/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h539 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h540 : z ≤ ((2289/16000 : ℚ) : ℝ)
    · -- left
      by_cases h541 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h542 : a ≤ ((13/32 : ℚ) : ℝ)
        · -- left
          by_cases h543 : z ≤ ((6417/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B033.c677_pos (not_le.mp h0).le h542 hz1 h543
          · -- right
            exact CKLaneC2R.Cells.S02.B033.c679_pos (not_le.mp h0).le h542 (not_le.mp h543).le h541
        · -- right
          by_cases h544 : z ≤ ((6417/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B033.c678_pos (not_le.mp h542).le h536 hz1 h544
          · -- right
            exact CKLaneC2R.Cells.S02.B034.c680_pos (not_le.mp h542).le h536 (not_le.mp h544).le h541
      · -- right
        by_cases h545 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          by_cases h546 : a ≤ ((13/32 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B034.c685_pos (not_le.mp h0).le h546 (not_le.mp h541).le h545
          · -- right
            exact CKLaneC2R.Cells.S02.B034.c686_pos (not_le.mp h546).le h536 (not_le.mp h541).le h545
        · -- right
          exact CKLaneC2R.Cells.S02.B020.c409_pos (not_le.mp h0).le h536 (not_le.mp h545).le h540
    · -- right
      by_cases h547 : z ≤ ((5491/32000 : ℚ) : ℝ)
      · -- left
        by_cases h548 : z ≤ ((10069/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B020.c417_pos (not_le.mp h0).le h536 (not_le.mp h540).le h548
        · -- right
          exact CKLaneC2R.Cells.S02.B020.c418_pos (not_le.mp h0).le h536 (not_le.mp h548).le h547
      · -- right
        by_cases h549 : z ≤ ((2379/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B021.c421_pos (not_le.mp h0).le h536 (not_le.mp h547).le h549
        · -- right
          exact CKLaneC2R.Cells.S02.B021.c422_pos (not_le.mp h0).le h536 (not_le.mp h549).le h539
  · -- right
    by_cases h550 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h551 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        by_cases h552 : a ≤ ((13/32 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B021.c433_pos (not_le.mp h0).le h552 (not_le.mp h539).le h551
        · -- right
          exact CKLaneC2R.Cells.S02.B021.c434_pos (not_le.mp h552).le h536 (not_le.mp h539).le h551
      · -- right
        exact CKLaneC2R.Cells.S02.B003.c65_pos (not_le.mp h0).le h536 (not_le.mp h551).le h550
    · -- right
      by_cases h553 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B003.c67_pos (not_le.mp h0).le h536 (not_le.mp h550).le h553
      · -- right
        exact CKLaneC2R.Cells.S02.B003.c68_pos (not_le.mp h0).le h536 (not_le.mp h553).le h538

end CKLaneC2R.CompactCover


