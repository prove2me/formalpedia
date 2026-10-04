-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g79
-- name    : CK_CKLaneC2R_CompactCover_S00_g79
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T02:28:04.458623+00:00
-- url     : https://prove2.me/theorems/2eb2e822-22b1-44ef-960f-516bbfb1558e
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B028
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B029
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B030
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B032
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B049

namespace CKLaneC2R.CompactCover

theorem strip0_s096 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : a ≤ ((29/160 : ℚ) : ℝ)) (h893 : ¬ (a ≤ ((57/320 : ℚ) : ℝ))) (h988 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1035 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1051 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1052 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h1053 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1054 : z ≤ ((50241/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B028.c579_pos (not_le.mp h893).le h892 (not_le.mp h1035).le h1054
      · -- right
        exact CKLaneC2R.Cells.S00.B029.c580_pos (not_le.mp h893).le h892 (not_le.mp h1054).le h1053
    · -- right
      by_cases h1055 : z ≤ ((52067/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B029.c583_pos (not_le.mp h893).le h892 (not_le.mp h1053).le h1055
      · -- right
        exact CKLaneC2R.Cells.S00.B029.c584_pos (not_le.mp h893).le h892 (not_le.mp h1055).le h1052
  · -- right
    by_cases h1056 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1057 : z ≤ ((53893/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B030.c608_pos (not_le.mp h893).le h892 (not_le.mp h1052).le h1057
      · -- right
        exact CKLaneC2R.Cells.S00.B030.c610_pos (not_le.mp h893).le h892 (not_le.mp h1057).le h1056
    · -- right
      by_cases h1058 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B030.c616_pos (not_le.mp h893).le h892 (not_le.mp h1056).le h1058
      · -- right
        exact CKLaneC2R.Cells.S00.B030.c618_pos (not_le.mp h893).le h892 (not_le.mp h1058).le h1051

theorem strip0_s097 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : a ≤ ((29/160 : ℚ) : ℝ)) (h893 : ¬ (a ≤ ((57/320 : ℚ) : ℝ))) (h988 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h1035 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h1051 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h1059 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1060 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h1061 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B032.c646_pos (not_le.mp h893).le h892 (not_le.mp h1051).le h1061
    · -- right
      exact CKLaneC2R.Cells.S00.B032.c648_pos (not_le.mp h893).le h892 (not_le.mp h1061).le h1060
  · -- right
    by_cases h1062 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B032.c653_pos (not_le.mp h893).le h892 (not_le.mp h1060).le h1062
    · -- right
      by_cases h1063 : z ≤ ((23931/25600 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B049.c985_pos (not_le.mp h893).le h892 (not_le.mp h1062).le h1063
      · -- right
        exact CKLaneC2R.Cells.S00.B049.c986_pos (not_le.mp h893).le h892 (not_le.mp h1063).le h1059

end CKLaneC2R.CompactCover


