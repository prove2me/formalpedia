-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g46
-- name    : CK_CKLaneC2R_CompactCover_S02_g46
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T11:15:00.885372+00:00
-- url     : https://prove2.me/theorems/c077d801-86bd-48e7-b30d-209f6945e918
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
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B003
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B004

namespace CKLaneC2R.CompactCover

theorem strip2_s068 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : ¬ (a ≤ ((9/20 : ℚ) : ℝ))) (h717 : a ≤ ((19/40 : ℚ) : ℝ)) (h718 : a ≤ ((37/80 : ℚ) : ℝ)) (h719 : z ≤ ((217/400 : ℚ) : ℝ)) (h720 : z ≤ ((1257/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h721 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h722 : z ≤ ((2289/16000 : ℚ) : ℝ)
    · -- left
      by_cases h723 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h724 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          by_cases h725 : a ≤ ((73/160 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B034.c693_pos (not_le.mp h534).le h725 hz1 h724
          · -- right
            exact CKLaneC2R.Cells.S02.B034.c694_pos (not_le.mp h725).le h718 hz1 h724
        · -- right
          exact CKLaneC2R.Cells.S02.B021.c437_pos (not_le.mp h534).le h718 (not_le.mp h724).le h723
      · -- right
        by_cases h726 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B021.c439_pos (not_le.mp h534).le h718 (not_le.mp h723).le h726
        · -- right
          exact CKLaneC2R.Cells.S02.B022.c440_pos (not_le.mp h534).le h718 (not_le.mp h726).le h722
    · -- right
      by_cases h727 : z ≤ ((5491/32000 : ℚ) : ℝ)
      · -- left
        by_cases h728 : z ≤ ((10069/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B022.c451_pos (not_le.mp h534).le h718 (not_le.mp h722).le h728
        · -- right
          exact CKLaneC2R.Cells.S02.B022.c452_pos (not_le.mp h534).le h718 (not_le.mp h728).le h727
      · -- right
        exact CKLaneC2R.Cells.S02.B003.c79_pos (not_le.mp h534).le h718 (not_le.mp h727).le h721
  · -- right
    by_cases h729 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h730 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B004.c84_pos (not_le.mp h534).le h718 (not_le.mp h721).le h730
      · -- right
        exact CKLaneC2R.Cells.S02.B004.c85_pos (not_le.mp h534).le h718 (not_le.mp h730).le h729
    · -- right
      by_cases h731 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B004.c88_pos (not_le.mp h534).le h718 (not_le.mp h729).le h731
      · -- right
        exact CKLaneC2R.Cells.S02.B004.c89_pos (not_le.mp h534).le h718 (not_le.mp h731).le h720

end CKLaneC2R.CompactCover


