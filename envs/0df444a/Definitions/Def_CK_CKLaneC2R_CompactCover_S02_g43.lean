-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g43
-- name    : CK_CKLaneC2R_CompactCover_S02_g43
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T09:27:04.479955+00:00
-- url     : https://prove2.me/theorems/cae75cd2-7d6a-435a-afa3-3d312e83d4de
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B034
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B021
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B003

namespace CKLaneC2R.CompactCover

theorem strip2_s064 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : a ≤ ((9/20 : ℚ) : ℝ)) (h535 : ¬ (a ≤ ((17/40 : ℚ) : ℝ))) (h630 : ¬ (a ≤ ((7/16 : ℚ) : ℝ))) (h675 : z ≤ ((217/400 : ℚ) : ℝ)) (h676 : z ≤ ((1257/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h677 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h678 : z ≤ ((2289/16000 : ℚ) : ℝ)
    · -- left
      by_cases h679 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h680 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          by_cases h681 : a ≤ ((71/160 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B034.c691_pos (not_le.mp h630).le h681 hz1 h680
          · -- right
            exact CKLaneC2R.Cells.S02.B034.c692_pos (not_le.mp h681).le h534 hz1 h680
        · -- right
          exact CKLaneC2R.Cells.S02.B020.c412_pos (not_le.mp h630).le h534 (not_le.mp h680).le h679
      · -- right
        by_cases h682 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B020.c415_pos (not_le.mp h630).le h534 (not_le.mp h679).le h682
        · -- right
          exact CKLaneC2R.Cells.S02.B020.c416_pos (not_le.mp h630).le h534 (not_le.mp h682).le h678
    · -- right
      by_cases h683 : z ≤ ((5491/32000 : ℚ) : ℝ)
      · -- left
        by_cases h684 : z ≤ ((10069/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B021.c427_pos (not_le.mp h630).le h534 (not_le.mp h678).le h684
        · -- right
          exact CKLaneC2R.Cells.S02.B021.c428_pos (not_le.mp h630).le h534 (not_le.mp h684).le h683
      · -- right
        by_cases h685 : z ≤ ((2379/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B021.c431_pos (not_le.mp h630).le h534 (not_le.mp h683).le h685
        · -- right
          exact CKLaneC2R.Cells.S02.B021.c432_pos (not_le.mp h630).le h534 (not_le.mp h685).le h677
  · -- right
    by_cases h686 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h687 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B003.c73_pos (not_le.mp h630).le h534 (not_le.mp h677).le h687
      · -- right
        exact CKLaneC2R.Cells.S02.B003.c74_pos (not_le.mp h630).le h534 (not_le.mp h687).le h686
    · -- right
      by_cases h688 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B003.c77_pos (not_le.mp h630).le h534 (not_le.mp h686).le h688
      · -- right
        exact CKLaneC2R.Cells.S02.B003.c78_pos (not_le.mp h630).le h534 (not_le.mp h688).le h676

end CKLaneC2R.CompactCover


