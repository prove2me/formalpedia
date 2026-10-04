-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g18
-- name    : CK_CKLaneC2R_CompactCover_S05_g18
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T06:41:37.933516+00:00
-- url     : https://prove2.me/theorems/c61453a5-a7c9-4f56-9fbb-711712eb7bb8
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B009
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B014

namespace CKLaneC2R.CompactCover

theorem strip5_s031 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : a ≤ ((3897/4000 : ℚ) : ℝ)) (h148 : ¬ (a ≤ ((1539/1600 : ℚ) : ℝ))) (h199 : ¬ (a ≤ ((15489/16000 : ℚ) : ℝ))) (h235 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h243 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h247 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h248 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h249 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B008.c171_pos (not_le.mp h199).le h147 (not_le.mp h243).le h249
    · -- right
      exact CKLaneC2R.Cells.S05.B008.c173_pos (not_le.mp h199).le h147 (not_le.mp h249).le h248
  · -- right
    by_cases h250 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B008.c179_pos (not_le.mp h199).le h147 (not_le.mp h248).le h250
    · -- right
      exact CKLaneC2R.Cells.S05.B009.c181_pos (not_le.mp h199).le h147 (not_le.mp h250).le h247

theorem strip5_s032 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : a ≤ ((3897/4000 : ℚ) : ℝ)) (h148 : ¬ (a ≤ ((1539/1600 : ℚ) : ℝ))) (h199 : ¬ (a ≤ ((15489/16000 : ℚ) : ℝ))) (h235 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h243 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h247 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h251 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h252 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h253 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B013.c275_pos (not_le.mp h199).le h147 (not_le.mp h247).le h253
    · -- right
      exact CKLaneC2R.Cells.S05.B013.c276_pos (not_le.mp h199).le h147 (not_le.mp h253).le h252
  · -- right
    by_cases h254 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B014.c283_pos (not_le.mp h199).le h147 (not_le.mp h252).le h254
    · -- right
      exact CKLaneC2R.Cells.S05.B014.c284_pos (not_le.mp h199).le h147 (not_le.mp h254).le h251

end CKLaneC2R.CompactCover


