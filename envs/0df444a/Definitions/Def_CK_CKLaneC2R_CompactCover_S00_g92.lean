-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g92
-- name    : CK_CKLaneC2R_CompactCover_S00_g92
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T18:35:35.035509+00:00
-- url     : https://prove2.me/theorems/06a14f66-67d9-4ace-af91-716294e3c9ec
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B044
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B045
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B009
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B011
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B012

namespace CKLaneC2R.CompactCover

theorem strip0_s115 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : a ≤ ((31/160 : ℚ) : ℝ)) (h1239 : z ≤ ((217/400 : ℚ) : ℝ)) (h1240 : a ≤ ((61/320 : ℚ) : ℝ)) (h1241 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1242 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h1243 : ¬ (z ≤ ((2289/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1254 : z ≤ ((5491/32000 : ℚ) : ℝ)
  · -- left
    by_cases h1255 : z ≤ ((10069/64000 : ℚ) : ℝ)
    · -- left
      by_cases h1256 : z ≤ ((769/5120 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B044.c893_pos (not_le.mp h891).le h1240 (not_le.mp h1243).le h1256
      · -- right
        exact CKLaneC2R.Cells.S00.B044.c894_pos (not_le.mp h891).le h1240 (not_le.mp h1256).le h1255
    · -- right
      by_cases h1257 : z ≤ ((21051/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B044.c897_pos (not_le.mp h891).le h1240 (not_le.mp h1255).le h1257
      · -- right
        exact CKLaneC2R.Cells.S00.B044.c898_pos (not_le.mp h891).le h1240 (not_le.mp h1257).le h1254
  · -- right
    by_cases h1258 : z ≤ ((2379/12800 : ℚ) : ℝ)
    · -- left
      by_cases h1259 : z ≤ ((22877/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B045.c909_pos (not_le.mp h891).le h1240 (not_le.mp h1254).le h1259
      · -- right
        exact CKLaneC2R.Cells.S00.B045.c910_pos (not_le.mp h891).le h1240 (not_le.mp h1259).le h1258
    · -- right
      exact CKLaneC2R.Cells.S00.B009.c199_pos (not_le.mp h891).le h1240 (not_le.mp h1258).le h1242

theorem strip0_s116 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : a ≤ ((31/160 : ℚ) : ℝ)) (h1239 : z ≤ ((217/400 : ℚ) : ℝ)) (h1240 : a ≤ ((61/320 : ℚ) : ℝ)) (h1241 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h1242 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1260 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h1261 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1262 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B011.c233_pos (not_le.mp h891).le h1240 (not_le.mp h1242).le h1262
      · -- right
        exact CKLaneC2R.Cells.S00.B011.c234_pos (not_le.mp h891).le h1240 (not_le.mp h1262).le h1261
    · -- right
      by_cases h1263 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B011.c237_pos (not_le.mp h891).le h1240 (not_le.mp h1261).le h1263
      · -- right
        exact CKLaneC2R.Cells.S00.B011.c238_pos (not_le.mp h891).le h1240 (not_le.mp h1263).le h1260
  · -- right
    by_cases h1264 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h1265 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B012.c249_pos (not_le.mp h891).le h1240 (not_le.mp h1260).le h1265
      · -- right
        exact CKLaneC2R.Cells.S00.B012.c250_pos (not_le.mp h891).le h1240 (not_le.mp h1265).le h1264
    · -- right
      by_cases h1266 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B012.c253_pos (not_le.mp h891).le h1240 (not_le.mp h1264).le h1266
      · -- right
        exact CKLaneC2R.Cells.S00.B012.c254_pos (not_le.mp h891).le h1240 (not_le.mp h1266).le h1241

end CKLaneC2R.CompactCover


