-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g41
-- name    : CK_CKLaneC2R_CompactCover_S05_g41
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T13:15:34.633061+00:00
-- url     : https://prove2.me/theorems/44162e6b-7ac5-4d43-8941-d1019034c47e
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B022
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B025
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B026
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B028

namespace CKLaneC2R.CompactCover

theorem strip5_s074 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : a ≤ ((31869/32000 : ℚ) : ℝ)) (h474 : a ≤ ((63639/64000 : ℚ) : ℝ)) (h475 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h480 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h483 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h486 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h489 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h490 : z ≤ ((61197/64000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B022.c454_pos (not_le.mp h376).le h474 (not_le.mp h486).le h490
  · -- right
    by_cases h491 : z ≤ ((123307/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B025.c505_pos (not_le.mp h376).le h474 (not_le.mp h490).le h491
    · -- right
      exact CKLaneC2R.Cells.S05.B025.c506_pos (not_le.mp h376).le h474 (not_le.mp h491).le h489

theorem strip5_s075 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : a ≤ ((31869/32000 : ℚ) : ℝ)) (h474 : a ≤ ((63639/64000 : ℚ) : ℝ)) (h475 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h480 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h483 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h486 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h489 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) (h492 : z ≤ ((63023/64000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h493 : z ≤ ((125133/128000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B026.c527_pos (not_le.mp h376).le h474 (not_le.mp h489).le h493
  · -- right
    by_cases h494 : z ≤ ((251179/256000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B028.c569_pos (not_le.mp h376).le h474 (not_le.mp h493).le h494
    · -- right
      exact CKLaneC2R.Cells.S05.B028.c570_pos (not_le.mp h376).le h474 (not_le.mp h494).le h492

end CKLaneC2R.CompactCover


