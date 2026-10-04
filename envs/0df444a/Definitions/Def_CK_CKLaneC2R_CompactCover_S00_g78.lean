-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g78
-- name    : CK_CKLaneC2R_CompactCover_S00_g78
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T19:55:10.325458+00:00
-- url     : https://prove2.me/theorems/e001c3a0-225f-4f5b-b000-026bb728c30d
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B023
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B024
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B025

namespace CKLaneC2R.CompactCover

theorem strip0_s095 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : a ≤ ((29/160 : ℚ) : ℝ)) (h893 : ¬ (a ≤ ((57/320 : ℚ) : ℝ))) (h988 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1035 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1036 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h1037 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1038 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1039 : z ≤ ((35633/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B023.c475_pos (not_le.mp h893).le h892 (not_le.mp h988).le h1039
        · -- right
          exact CKLaneC2R.Cells.S00.B023.c476_pos (not_le.mp h893).le h892 (not_le.mp h1039).le h1038
      · -- right
        by_cases h1040 : z ≤ ((37459/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B023.c479_pos (not_le.mp h893).le h892 (not_le.mp h1038).le h1040
        · -- right
          exact CKLaneC2R.Cells.S00.B024.c480_pos (not_le.mp h893).le h892 (not_le.mp h1040).le h1037
    · -- right
      by_cases h1041 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1042 : z ≤ ((7857/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B024.c483_pos (not_le.mp h893).le h892 (not_le.mp h1037).le h1042
        · -- right
          exact CKLaneC2R.Cells.S00.B024.c484_pos (not_le.mp h893).le h892 (not_le.mp h1042).le h1041
      · -- right
        by_cases h1043 : z ≤ ((41111/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B024.c487_pos (not_le.mp h893).le h892 (not_le.mp h1041).le h1043
        · -- right
          exact CKLaneC2R.Cells.S00.B024.c488_pos (not_le.mp h893).le h892 (not_le.mp h1043).le h1036
  · -- right
    by_cases h1044 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1045 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        by_cases h1046 : z ≤ ((42937/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B024.c491_pos (not_le.mp h893).le h892 (not_le.mp h1036).le h1046
        · -- right
          exact CKLaneC2R.Cells.S00.B024.c492_pos (not_le.mp h893).le h892 (not_le.mp h1046).le h1045
      · -- right
        by_cases h1047 : z ≤ ((44763/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B024.c495_pos (not_le.mp h893).le h892 (not_le.mp h1045).le h1047
        · -- right
          exact CKLaneC2R.Cells.S00.B024.c496_pos (not_le.mp h893).le h892 (not_le.mp h1047).le h1044
    · -- right
      by_cases h1048 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1049 : z ≤ ((46589/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B025.c501_pos (not_le.mp h893).le h892 (not_le.mp h1044).le h1049
        · -- right
          exact CKLaneC2R.Cells.S00.B025.c502_pos (not_le.mp h893).le h892 (not_le.mp h1049).le h1048
      · -- right
        by_cases h1050 : z ≤ ((9683/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B025.c505_pos (not_le.mp h893).le h892 (not_le.mp h1048).le h1050
        · -- right
          exact CKLaneC2R.Cells.S00.B025.c506_pos (not_le.mp h893).le h892 (not_le.mp h1050).le h1035

end CKLaneC2R.CompactCover


