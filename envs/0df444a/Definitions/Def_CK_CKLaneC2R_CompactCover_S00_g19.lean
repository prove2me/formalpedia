-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g19
-- name    : CK_CKLaneC2R_CompactCover_S00_g19
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T01:08:39.402299+00:00
-- url     : https://prove2.me/theorems/502d377c-827c-474b-8c69-22a01646bd08
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B049
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B050
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B064

namespace CKLaneC2R.CompactCover

theorem strip0_s024 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((49/320 : ℚ) : ℝ))) (h133 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h202 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h218 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h227 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h235 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h236 : z ≤ ((61197/64000 : ℚ) : ℝ)
  · -- left
    by_cases h237 : z ≤ ((121481/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B049.c996_pos (not_le.mp h3).le h2 (not_le.mp h227).le h237
    · -- right
      exact CKLaneC2R.Cells.S00.B049.c998_pos (not_le.mp h3).le h2 (not_le.mp h237).le h236
  · -- right
    by_cases h238 : z ≤ ((123307/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B050.c1003_pos (not_le.mp h3).le h2 (not_le.mp h236).le h238
    · -- right
      by_cases h239 : z ≤ ((247527/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B064.c1293_pos (not_le.mp h3).le h2 (not_le.mp h238).le h239
      · -- right
        exact CKLaneC2R.Cells.S00.B064.c1294_pos (not_le.mp h3).le h2 (not_le.mp h239).le h235

end CKLaneC2R.CompactCover


