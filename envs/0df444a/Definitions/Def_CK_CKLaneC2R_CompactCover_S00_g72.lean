-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g72
-- name    : CK_CKLaneC2R_CompactCover_S00_g72
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T01:10:45.903192+00:00
-- url     : https://prove2.me/theorems/992a9987-7561-458a-ad67-4291ceb02e40
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

theorem strip0_s087 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : a ≤ ((29/160 : ℚ) : ℝ)) (h893 : a ≤ ((57/320 : ℚ) : ℝ)) (h894 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h943 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h959 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h960 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h961 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      by_cases h962 : z ≤ ((50241/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B028.c577_pos (not_le.mp h0).le h893 (not_le.mp h943).le h962
      · -- right
        exact CKLaneC2R.Cells.S00.B028.c578_pos (not_le.mp h0).le h893 (not_le.mp h962).le h961
    · -- right
      by_cases h963 : z ≤ ((52067/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B029.c581_pos (not_le.mp h0).le h893 (not_le.mp h961).le h963
      · -- right
        exact CKLaneC2R.Cells.S00.B029.c582_pos (not_le.mp h0).le h893 (not_le.mp h963).le h960
  · -- right
    by_cases h964 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      by_cases h965 : z ≤ ((53893/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B030.c607_pos (not_le.mp h0).le h893 (not_le.mp h960).le h965
      · -- right
        exact CKLaneC2R.Cells.S00.B030.c609_pos (not_le.mp h0).le h893 (not_le.mp h965).le h964
    · -- right
      by_cases h966 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B030.c615_pos (not_le.mp h0).le h893 (not_le.mp h964).le h966
      · -- right
        exact CKLaneC2R.Cells.S00.B030.c617_pos (not_le.mp h0).le h893 (not_le.mp h966).le h959

theorem strip0_s088 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : a ≤ ((29/160 : ℚ) : ℝ)) (h893 : a ≤ ((57/320 : ℚ) : ℝ)) (h894 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h943 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h959 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h967 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h968 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h969 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B032.c645_pos (not_le.mp h0).le h893 (not_le.mp h959).le h969
    · -- right
      exact CKLaneC2R.Cells.S00.B032.c647_pos (not_le.mp h0).le h893 (not_le.mp h969).le h968
  · -- right
    by_cases h970 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      by_cases h971 : z ≤ ((117829/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B049.c981_pos (not_le.mp h0).le h893 (not_le.mp h968).le h971
      · -- right
        exact CKLaneC2R.Cells.S00.B049.c982_pos (not_le.mp h0).le h893 (not_le.mp h971).le h970
    · -- right
      by_cases h972 : z ≤ ((23931/25600 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B049.c983_pos (not_le.mp h0).le h893 (not_le.mp h970).le h972
      · -- right
        exact CKLaneC2R.Cells.S00.B049.c984_pos (not_le.mp h0).le h893 (not_le.mp h972).le h967

end CKLaneC2R.CompactCover


