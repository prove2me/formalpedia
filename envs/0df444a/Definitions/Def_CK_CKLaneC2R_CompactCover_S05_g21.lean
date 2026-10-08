-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g21
-- name    : CK_CKLaneC2R_CompactCover_S05_g21
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T13:56:05.300885+00:00
-- url     : https://prove2.me/theorems/39843667-e515-426a-ac89-65e0fd5da286
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B009
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B011
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B017

namespace CKLaneC2R.CompactCover

theorem strip5_s037 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : a ≤ ((7893/8000 : ℚ) : ℝ)) (h272 : a ≤ ((15687/16000 : ℚ) : ℝ)) (h273 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h282 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h286 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h287 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h288 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B009.c182_pos (not_le.mp h147).le h272 (not_le.mp h282).le h288
    · -- right
      exact CKLaneC2R.Cells.S05.B009.c183_pos (not_le.mp h147).le h272 (not_le.mp h288).le h287
  · -- right
    by_cases h289 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B009.c186_pos (not_le.mp h147).le h272 (not_le.mp h287).le h289
    · -- right
      by_cases h290 : a ≤ ((1251/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B011.c235_pos (not_le.mp h147).le h290 (not_le.mp h289).le h286
      · -- right
        exact CKLaneC2R.Cells.S05.B011.c236_pos (not_le.mp h290).le h272 (not_le.mp h289).le h286

theorem strip5_s038 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : a ≤ ((7893/8000 : ℚ) : ℝ)) (h272 : a ≤ ((15687/16000 : ℚ) : ℝ)) (h273 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h282 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h286 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h291 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h292 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h293 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B014.c285_pos (not_le.mp h147).le h272 (not_le.mp h286).le h293
    · -- right
      exact CKLaneC2R.Cells.S05.B014.c286_pos (not_le.mp h147).le h272 (not_le.mp h293).le h292
  · -- right
    by_cases h294 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B014.c289_pos (not_le.mp h147).le h272 (not_le.mp h292).le h294
    · -- right
      by_cases h295 : a ≤ ((1251/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B017.c343_pos (not_le.mp h147).le h295 (not_le.mp h294).le h291
      · -- right
        exact CKLaneC2R.Cells.S05.B017.c344_pos (not_le.mp h295).le h272 (not_le.mp h294).le h291

end CKLaneC2R.CompactCover


