-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g49
-- name    : CK_CKLaneC2R_CompactCover_S02_g49
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T07:43:18.473277+00:00
-- url     : https://prove2.me/theorems/068c5e39-fa9b-4a62-9b5a-ea3487e08d87
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
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B021
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B022
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B004

namespace CKLaneC2R.CompactCover

theorem strip2_s072 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : ¬ (a ≤ ((9/20 : ℚ) : ℝ))) (h717 : a ≤ ((19/40 : ℚ) : ℝ)) (h718 : ¬ (a ≤ ((37/80 : ℚ) : ℝ))) (h756 : z ≤ ((217/400 : ℚ) : ℝ)) (h757 : z ≤ ((1257/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h758 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h759 : z ≤ ((2289/16000 : ℚ) : ℝ)
    · -- left
      by_cases h760 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h761 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          by_cases h762 : a ≤ ((15/32 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B034.c695_pos (not_le.mp h718).le h762 hz1 h761
          · -- right
            exact CKLaneC2R.Cells.S02.B034.c696_pos (not_le.mp h762).le h717 hz1 h761
        · -- right
          exact CKLaneC2R.Cells.S02.B021.c438_pos (not_le.mp h718).le h717 (not_le.mp h761).le h760
      · -- right
        by_cases h763 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B022.c441_pos (not_le.mp h718).le h717 (not_le.mp h760).le h763
        · -- right
          exact CKLaneC2R.Cells.S02.B022.c442_pos (not_le.mp h718).le h717 (not_le.mp h763).le h759
    · -- right
      by_cases h764 : z ≤ ((5491/32000 : ℚ) : ℝ)
      · -- left
        by_cases h765 : z ≤ ((10069/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B022.c453_pos (not_le.mp h718).le h717 (not_le.mp h759).le h765
        · -- right
          exact CKLaneC2R.Cells.S02.B022.c454_pos (not_le.mp h718).le h717 (not_le.mp h765).le h764
      · -- right
        exact CKLaneC2R.Cells.S02.B004.c80_pos (not_le.mp h718).le h717 (not_le.mp h764).le h758
  · -- right
    by_cases h766 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h767 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B004.c86_pos (not_le.mp h718).le h717 (not_le.mp h758).le h767
      · -- right
        exact CKLaneC2R.Cells.S02.B004.c87_pos (not_le.mp h718).le h717 (not_le.mp h767).le h766
    · -- right
      by_cases h768 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B004.c90_pos (not_le.mp h718).le h717 (not_le.mp h766).le h768
      · -- right
        exact CKLaneC2R.Cells.S02.B004.c91_pos (not_le.mp h718).le h717 (not_le.mp h768).le h757

end CKLaneC2R.CompactCover


