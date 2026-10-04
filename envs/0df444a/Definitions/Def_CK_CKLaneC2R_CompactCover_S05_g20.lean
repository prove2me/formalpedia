-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g20
-- name    : CK_CKLaneC2R_CompactCover_S05_g20
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T19:13:46.085277+00:00
-- url     : https://prove2.me/theorems/9a32806b-d306-4bc1-9475-fbdd90d6ed71
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S05 (proof part of strip5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S05 (proof part of strip5).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B003
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B004
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B005

namespace CKLaneC2R.CompactCover

theorem strip5_s035 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : a ≤ ((7893/8000 : ℚ) : ℝ)) (h272 : a ≤ ((15687/16000 : ℚ) : ℝ)) (h273 : z ≤ ((217/400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h274 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h275 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h276 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        by_cases h277 : a ≤ ((1251/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B006.c130_pos (not_le.mp h147).le h277 hz1 h276
        · -- right
          exact CKLaneC2R.Cells.S05.B006.c131_pos (not_le.mp h277).le h272 hz1 h276
      · -- right
        exact CKLaneC2R.Cells.S05.B003.c76_pos (not_le.mp h147).le h272 (not_le.mp h276).le h275
    · -- right
      by_cases h278 : z ≤ ((823/3200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B003.c77_pos (not_le.mp h147).le h272 (not_le.mp h275).le h278
      · -- right
        exact CKLaneC2R.Cells.S05.B003.c78_pos (not_le.mp h147).le h272 (not_le.mp h278).le h274
  · -- right
    by_cases h279 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h280 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B004.c81_pos (not_le.mp h147).le h272 (not_le.mp h274).le h280
      · -- right
        exact CKLaneC2R.Cells.S05.B004.c82_pos (not_le.mp h147).le h272 (not_le.mp h280).le h279
    · -- right
      by_cases h281 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B004.c85_pos (not_le.mp h147).le h272 (not_le.mp h279).le h281
      · -- right
        exact CKLaneC2R.Cells.S05.B004.c86_pos (not_le.mp h147).le h272 (not_le.mp h281).le h273

theorem strip5_s036 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : a ≤ ((7893/8000 : ℚ) : ℝ)) (h272 : a ≤ ((15687/16000 : ℚ) : ℝ)) (h273 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h282 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h283 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h284 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B005.c111_pos (not_le.mp h147).le h272 (not_le.mp h273).le h284
    · -- right
      exact CKLaneC2R.Cells.S05.B005.c112_pos (not_le.mp h147).le h272 (not_le.mp h284).le h283
  · -- right
    by_cases h285 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B005.c113_pos (not_le.mp h147).le h272 (not_le.mp h283).le h285
    · -- right
      exact CKLaneC2R.Cells.S05.B005.c114_pos (not_le.mp h147).le h272 (not_le.mp h285).le h282

end CKLaneC2R.CompactCover


