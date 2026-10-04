-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g68
-- name    : CK_CKLaneC2R_CompactCover_S00_g68
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T16:51:17.482274+00:00
-- url     : https://prove2.me/theorems/109bd4e6-f4cf-4d7d-9e61-0d4c0f83f575
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B061
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B062
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B063
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B041

namespace CKLaneC2R.CompactCover

theorem strip0_s082 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : a ≤ ((29/160 : ℚ) : ℝ)) (h893 : a ≤ ((57/320 : ℚ) : ℝ)) (h894 : z ≤ ((217/400 : ℚ) : ℝ)) (h895 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h896 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h897 : z ≤ ((2289/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h898 : z ≤ ((733/6400 : ℚ) : ℝ)
  · -- left
    by_cases h899 : a ≤ ((113/640 : ℚ) : ℝ)
    · -- left
      by_cases h900 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h901 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B061.c1225_pos (not_le.mp h0).le h899 hz1 h901
        · -- right
          exact CKLaneC2R.Cells.S00.B061.c1227_pos (not_le.mp h0).le h899 (not_le.mp h901).le h900
      · -- right
        by_cases h902 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B061.c1233_pos (not_le.mp h0).le h899 (not_le.mp h900).le h902
        · -- right
          exact CKLaneC2R.Cells.S00.B061.c1235_pos (not_le.mp h0).le h899 (not_le.mp h902).le h898
    · -- right
      by_cases h903 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h904 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B061.c1226_pos (not_le.mp h899).le h893 hz1 h904
        · -- right
          exact CKLaneC2R.Cells.S00.B061.c1228_pos (not_le.mp h899).le h893 (not_le.mp h904).le h903
      · -- right
        by_cases h905 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B061.c1234_pos (not_le.mp h899).le h893 (not_le.mp h903).le h905
        · -- right
          exact CKLaneC2R.Cells.S00.B061.c1236_pos (not_le.mp h899).le h893 (not_le.mp h905).le h898
  · -- right
    by_cases h906 : z ≤ ((8243/64000 : ℚ) : ℝ)
    · -- left
      by_cases h907 : a ≤ ((113/640 : ℚ) : ℝ)
      · -- left
        by_cases h908 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B062.c1257_pos (not_le.mp h0).le h907 (not_le.mp h898).le h908
        · -- right
          exact CKLaneC2R.Cells.S00.B062.c1259_pos (not_le.mp h0).le h907 (not_le.mp h908).le h906
      · -- right
        by_cases h909 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B062.c1258_pos (not_le.mp h907).le h893 (not_le.mp h898).le h909
        · -- right
          exact CKLaneC2R.Cells.S00.B063.c1260_pos (not_le.mp h907).le h893 (not_le.mp h909).le h906
    · -- right
      by_cases h910 : z ≤ ((17399/128000 : ℚ) : ℝ)
      · -- left
        by_cases h911 : a ≤ ((113/640 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B063.c1265_pos (not_le.mp h0).le h911 (not_le.mp h906).le h910
        · -- right
          exact CKLaneC2R.Cells.S00.B063.c1266_pos (not_le.mp h911).le h893 (not_le.mp h906).le h910
      · -- right
        exact CKLaneC2R.Cells.S00.B041.c829_pos (not_le.mp h0).le h893 (not_le.mp h910).le h897

end CKLaneC2R.CompactCover


