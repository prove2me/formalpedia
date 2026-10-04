-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g50
-- name    : CK_CKLaneC2R_CompactCover_S00_g50
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T18:30:03.819704+00:00
-- url     : https://prove2.me/theorems/6f99114d-3dcc-4e42-b500-2225cb128d81
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B026
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B028
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B032
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B048

namespace CKLaneC2R.CompactCover

theorem strip0_s060 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : a ≤ ((27/160 : ℚ) : ℝ)) (h482 : ¬ (a ≤ ((53/320 : ℚ) : ℝ))) (h590 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h645 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h661 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h662 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h663 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      by_cases h664 : z ≤ ((50241/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B026.c535_pos (not_le.mp h482).le h481 (not_le.mp h645).le h664
      · -- right
        exact CKLaneC2R.Cells.S00.B026.c536_pos (not_le.mp h482).le h481 (not_le.mp h664).le h663
    · -- right
      by_cases h665 : z ≤ ((52067/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B026.c539_pos (not_le.mp h482).le h481 (not_le.mp h663).le h665
      · -- right
        exact CKLaneC2R.Cells.S00.B027.c540_pos (not_le.mp h482).le h481 (not_le.mp h665).le h662
  · -- right
    by_cases h666 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      by_cases h667 : z ≤ ((53893/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B028.c563_pos (not_le.mp h482).le h481 (not_le.mp h662).le h667
      · -- right
        exact CKLaneC2R.Cells.S00.B028.c564_pos (not_le.mp h482).le h481 (not_le.mp h667).le h666
    · -- right
      by_cases h668 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B028.c570_pos (not_le.mp h482).le h481 (not_le.mp h666).le h668
      · -- right
        exact CKLaneC2R.Cells.S00.B028.c572_pos (not_le.mp h482).le h481 (not_le.mp h668).le h661

theorem strip0_s061 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : a ≤ ((27/160 : ℚ) : ℝ)) (h482 : ¬ (a ≤ ((53/320 : ℚ) : ℝ))) (h590 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h645 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h661 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h669 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h670 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h671 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B032.c640_pos (not_le.mp h482).le h481 (not_le.mp h661).le h671
    · -- right
      by_cases h672 : z ≤ ((116003/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B048.c963_pos (not_le.mp h482).le h481 (not_le.mp h671).le h672
      · -- right
        exact CKLaneC2R.Cells.S00.B048.c964_pos (not_le.mp h482).le h481 (not_le.mp h672).le h670
  · -- right
    by_cases h673 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      by_cases h674 : z ≤ ((117829/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B048.c967_pos (not_le.mp h482).le h481 (not_le.mp h670).le h674
      · -- right
        exact CKLaneC2R.Cells.S00.B048.c968_pos (not_le.mp h482).le h481 (not_le.mp h674).le h673
    · -- right
      by_cases h675 : z ≤ ((23931/25600 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B048.c971_pos (not_le.mp h482).le h481 (not_le.mp h673).le h675
      · -- right
        exact CKLaneC2R.Cells.S00.B048.c972_pos (not_le.mp h482).le h481 (not_le.mp h675).le h669

end CKLaneC2R.CompactCover


