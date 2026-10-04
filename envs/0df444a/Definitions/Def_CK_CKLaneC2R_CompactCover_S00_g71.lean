-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g71
-- name    : CK_CKLaneC2R_CompactCover_S00_g71
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T14:39:38.535712+00:00
-- url     : https://prove2.me/theorems/941f7227-2bf4-4932-8917-2f064c9ada90
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

theorem strip0_s086 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : a ≤ ((29/160 : ℚ) : ℝ)) (h893 : a ≤ ((57/320 : ℚ) : ℝ)) (h894 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h943 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h944 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h945 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h946 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        by_cases h947 : z ≤ ((35633/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B023.c473_pos (not_le.mp h0).le h893 (not_le.mp h894).le h947
        · -- right
          exact CKLaneC2R.Cells.S00.B023.c474_pos (not_le.mp h0).le h893 (not_le.mp h947).le h946
      · -- right
        by_cases h948 : z ≤ ((37459/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B023.c477_pos (not_le.mp h0).le h893 (not_le.mp h946).le h948
        · -- right
          exact CKLaneC2R.Cells.S00.B023.c478_pos (not_le.mp h0).le h893 (not_le.mp h948).le h945
    · -- right
      by_cases h949 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        by_cases h950 : z ≤ ((7857/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B024.c481_pos (not_le.mp h0).le h893 (not_le.mp h945).le h950
        · -- right
          exact CKLaneC2R.Cells.S00.B024.c482_pos (not_le.mp h0).le h893 (not_le.mp h950).le h949
      · -- right
        by_cases h951 : z ≤ ((41111/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B024.c485_pos (not_le.mp h0).le h893 (not_le.mp h949).le h951
        · -- right
          exact CKLaneC2R.Cells.S00.B024.c486_pos (not_le.mp h0).le h893 (not_le.mp h951).le h944
  · -- right
    by_cases h952 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h953 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        by_cases h954 : z ≤ ((42937/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B024.c489_pos (not_le.mp h0).le h893 (not_le.mp h944).le h954
        · -- right
          exact CKLaneC2R.Cells.S00.B024.c490_pos (not_le.mp h0).le h893 (not_le.mp h954).le h953
      · -- right
        by_cases h955 : z ≤ ((44763/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B024.c493_pos (not_le.mp h0).le h893 (not_le.mp h953).le h955
        · -- right
          exact CKLaneC2R.Cells.S00.B024.c494_pos (not_le.mp h0).le h893 (not_le.mp h955).le h952
    · -- right
      by_cases h956 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        by_cases h957 : z ≤ ((46589/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B024.c499_pos (not_le.mp h0).le h893 (not_le.mp h952).le h957
        · -- right
          exact CKLaneC2R.Cells.S00.B025.c500_pos (not_le.mp h0).le h893 (not_le.mp h957).le h956
      · -- right
        by_cases h958 : z ≤ ((9683/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B025.c503_pos (not_le.mp h0).le h893 (not_le.mp h956).le h958
        · -- right
          exact CKLaneC2R.Cells.S00.B025.c504_pos (not_le.mp h0).le h893 (not_le.mp h958).le h943

end CKLaneC2R.CompactCover


