-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g93
-- name    : CK_CKLaneC2R_CompactCover_S00_g93
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T02:16:11.019629+00:00
-- url     : https://prove2.me/theorems/efa4db47-5bfb-4460-ad4d-6526ee9628fa
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B015
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B000

namespace CKLaneC2R.CompactCover

theorem strip0_s117 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : ¬ (a ≤ ((3/16 : ℚ) : ℝ))) (h1238 : a ≤ ((31/160 : ℚ) : ℝ)) (h1239 : z ≤ ((217/400 : ℚ) : ℝ)) (h1240 : a ≤ ((61/320 : ℚ) : ℝ)) (h1241 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h1267 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h1268 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1269 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h1270 : z ≤ ((841/2560 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B014.c297_pos (not_le.mp h891).le h1240 (not_le.mp h1241).le h1270
        · -- right
          exact CKLaneC2R.Cells.S00.B014.c298_pos (not_le.mp h891).le h1240 (not_le.mp h1270).le h1269
      · -- right
        by_cases h1271 : z ≤ ((22851/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B015.c301_pos (not_le.mp h891).le h1240 (not_le.mp h1269).le h1271
        · -- right
          exact CKLaneC2R.Cells.S00.B015.c302_pos (not_le.mp h891).le h1240 (not_le.mp h1271).le h1268
    · -- right
      by_cases h1272 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        by_cases h1273 : z ≤ ((24677/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B015.c313_pos (not_le.mp h891).le h1240 (not_le.mp h1268).le h1273
        · -- right
          exact CKLaneC2R.Cells.S00.B015.c314_pos (not_le.mp h891).le h1240 (not_le.mp h1273).le h1272
      · -- right
        by_cases h1274 : z ≤ ((26503/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B015.c317_pos (not_le.mp h891).le h1240 (not_le.mp h1272).le h1274
        · -- right
          exact CKLaneC2R.Cells.S00.B015.c318_pos (not_le.mp h891).le h1240 (not_le.mp h1274).le h1267
  · -- right
    by_cases h1275 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h1276 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B000.c8_pos (not_le.mp h891).le h1240 (not_le.mp h1267).le h1276
      · -- right
        exact CKLaneC2R.Cells.S00.B000.c10_pos (not_le.mp h891).le h1240 (not_le.mp h1276).le h1275
    · -- right
      by_cases h1277 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B000.c16_pos (not_le.mp h891).le h1240 (not_le.mp h1275).le h1277
      · -- right
        exact CKLaneC2R.Cells.S00.B000.c18_pos (not_le.mp h891).le h1240 (not_le.mp h1277).le h1239

end CKLaneC2R.CompactCover


