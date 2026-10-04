-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g07
-- name    : CK_CKLaneC2R_CompactCover_S00_g07
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T09:42:46.068983+00:00
-- url     : https://prove2.me/theorems/375811e6-330d-49e5-92fe-46aa46ea9911
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B025
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B026
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B046
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B047

namespace CKLaneC2R.CompactCover

theorem strip0_s009 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : a ≤ ((49/320 : ℚ) : ℝ)) (h4 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h78 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h94 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h95 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h96 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      by_cases h97 : z ≤ ((50241/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B025.c517_pos ha1 h3 (not_le.mp h78).le h97
      · -- right
        exact CKLaneC2R.Cells.S00.B025.c518_pos ha1 h3 (not_le.mp h97).le h96
    · -- right
      by_cases h98 : z ≤ ((52067/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B026.c521_pos ha1 h3 (not_le.mp h96).le h98
      · -- right
        exact CKLaneC2R.Cells.S00.B026.c522_pos ha1 h3 (not_le.mp h98).le h95
  · -- right
    by_cases h99 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      by_cases h100 : z ≤ ((53893/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B027.c549_pos ha1 h3 (not_le.mp h95).le h100
      · -- right
        by_cases h101 : a ≤ ((97/640 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B046.c921_pos ha1 h101 (not_le.mp h100).le h99
        · -- right
          exact CKLaneC2R.Cells.S00.B046.c922_pos (not_le.mp h101).le h3 (not_le.mp h100).le h99
    · -- right
      by_cases h102 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        by_cases h103 : z ≤ ((4421/5120 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B046.c923_pos ha1 h3 (not_le.mp h99).le h103
        · -- right
          exact CKLaneC2R.Cells.S00.B046.c924_pos ha1 h3 (not_le.mp h103).le h102
      · -- right
        by_cases h104 : z ≤ ((112351/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B046.c925_pos ha1 h3 (not_le.mp h102).le h104
        · -- right
          exact CKLaneC2R.Cells.S00.B046.c926_pos ha1 h3 (not_le.mp h104).le h94

theorem strip0_s010 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : a ≤ ((49/320 : ℚ) : ℝ)) (h4 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h78 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h94 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h105 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h106 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h107 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      by_cases h108 : z ≤ ((114177/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B046.c929_pos ha1 h3 (not_le.mp h94).le h108
      · -- right
        exact CKLaneC2R.Cells.S00.B046.c930_pos ha1 h3 (not_le.mp h108).le h107
    · -- right
      by_cases h109 : z ≤ ((116003/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B046.c933_pos ha1 h3 (not_le.mp h107).le h109
      · -- right
        exact CKLaneC2R.Cells.S00.B046.c934_pos ha1 h3 (not_le.mp h109).le h106
  · -- right
    by_cases h110 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      by_cases h111 : z ≤ ((117829/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B047.c945_pos ha1 h3 (not_le.mp h106).le h111
      · -- right
        exact CKLaneC2R.Cells.S00.B047.c946_pos ha1 h3 (not_le.mp h111).le h110
    · -- right
      by_cases h112 : z ≤ ((23931/25600 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B047.c949_pos ha1 h3 (not_le.mp h110).le h112
      · -- right
        exact CKLaneC2R.Cells.S00.B047.c950_pos ha1 h3 (not_le.mp h112).le h105

end CKLaneC2R.CompactCover


