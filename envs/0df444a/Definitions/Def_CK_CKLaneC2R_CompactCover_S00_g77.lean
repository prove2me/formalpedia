-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g77
-- name    : CK_CKLaneC2R_CompactCover_S00_g77
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T06:22:10.212385+00:00
-- url     : https://prove2.me/theorems/e351da5e-df12-49a3-a45a-d8e8dadfee04
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B017

namespace CKLaneC2R.CompactCover

theorem strip0_s094 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : a ≤ ((29/160 : ℚ) : ℝ)) (h893 : ¬ (a ≤ ((57/320 : ℚ) : ℝ))) (h988 : z ≤ ((217/400 : ℚ) : ℝ)) (h989 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1020 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h1021 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1022 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1023 : z ≤ ((841/2560 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B013.c267_pos (not_le.mp h893).le h892 (not_le.mp h989).le h1023
        · -- right
          exact CKLaneC2R.Cells.S00.B013.c268_pos (not_le.mp h893).le h892 (not_le.mp h1023).le h1022
      · -- right
        by_cases h1024 : z ≤ ((22851/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B013.c271_pos (not_le.mp h893).le h892 (not_le.mp h1022).le h1024
        · -- right
          exact CKLaneC2R.Cells.S00.B013.c272_pos (not_le.mp h893).le h892 (not_le.mp h1024).le h1021
    · -- right
      by_cases h1025 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        by_cases h1026 : z ≤ ((24677/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B014.c283_pos (not_le.mp h893).le h892 (not_le.mp h1021).le h1026
        · -- right
          exact CKLaneC2R.Cells.S00.B014.c284_pos (not_le.mp h893).le h892 (not_le.mp h1026).le h1025
      · -- right
        by_cases h1027 : z ≤ ((26503/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B014.c287_pos (not_le.mp h893).le h892 (not_le.mp h1025).le h1027
        · -- right
          exact CKLaneC2R.Cells.S00.B014.c288_pos (not_le.mp h893).le h892 (not_le.mp h1027).le h1020
  · -- right
    by_cases h1028 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1029 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1030 : z ≤ ((28329/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B016.c323_pos (not_le.mp h893).le h892 (not_le.mp h1020).le h1030
        · -- right
          exact CKLaneC2R.Cells.S00.B016.c324_pos (not_le.mp h893).le h892 (not_le.mp h1030).le h1029
      · -- right
        by_cases h1031 : z ≤ ((6031/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B016.c327_pos (not_le.mp h893).le h892 (not_le.mp h1029).le h1031
        · -- right
          exact CKLaneC2R.Cells.S00.B016.c328_pos (not_le.mp h893).le h892 (not_le.mp h1031).le h1028
    · -- right
      by_cases h1032 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1033 : z ≤ ((31981/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B016.c337_pos (not_le.mp h893).le h892 (not_le.mp h1028).le h1033
        · -- right
          exact CKLaneC2R.Cells.S00.B016.c338_pos (not_le.mp h893).le h892 (not_le.mp h1033).le h1032
      · -- right
        by_cases h1034 : z ≤ ((33807/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B017.c341_pos (not_le.mp h893).le h892 (not_le.mp h1032).le h1034
        · -- right
          exact CKLaneC2R.Cells.S00.B017.c342_pos (not_le.mp h893).le h892 (not_le.mp h1034).le h988

end CKLaneC2R.CompactCover


