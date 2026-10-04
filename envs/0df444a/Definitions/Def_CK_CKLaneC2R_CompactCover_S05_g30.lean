-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g30
-- name    : CK_CKLaneC2R_CompactCover_S05_g30
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T03:25:12.191304+00:00
-- url     : https://prove2.me/theorems/fa13c7f3-7879-46e7-ad2f-d8ba03f631a7
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B011
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B012
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B022

namespace CKLaneC2R.CompactCover

theorem strip5_s054 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : a ≤ ((3177/3200 : ℚ) : ℝ)) (h377 : a ≤ ((31671/32000 : ℚ) : ℝ)) (h378 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h385 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h389 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h390 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h391 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B011.c239_pos (not_le.mp h271).le h377 (not_le.mp h385).le h391
    · -- right
      exact CKLaneC2R.Cells.S05.B012.c240_pos (not_le.mp h271).le h377 (not_le.mp h391).le h390
  · -- right
    by_cases h392 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B012.c243_pos (not_le.mp h271).le h377 (not_le.mp h390).le h392
    · -- right
      exact CKLaneC2R.Cells.S05.B012.c244_pos (not_le.mp h271).le h377 (not_le.mp h392).le h389

theorem strip5_s055 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : a ≤ ((3177/3200 : ℚ) : ℝ)) (h377 : a ≤ ((31671/32000 : ℚ) : ℝ)) (h378 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h385 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h389 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h393 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h394 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h395 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B017.c349_pos (not_le.mp h271).le h377 (not_le.mp h389).le h395
    · -- right
      exact CKLaneC2R.Cells.S05.B017.c350_pos (not_le.mp h271).le h377 (not_le.mp h395).le h394
  · -- right
    by_cases h396 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B017.c353_pos (not_le.mp h271).le h377 (not_le.mp h394).le h396
    · -- right
      exact CKLaneC2R.Cells.S05.B017.c354_pos (not_le.mp h271).le h377 (not_le.mp h396).le h393

theorem strip5_s056 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : a ≤ ((3177/3200 : ℚ) : ℝ)) (h377 : a ≤ ((31671/32000 : ℚ) : ℝ)) (h378 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h385 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h389 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h393 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h397 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h398 : z ≤ ((61197/64000 : ℚ) : ℝ)
  · -- left
    by_cases h399 : z ≤ ((121481/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B022.c448_pos (not_le.mp h271).le h377 (not_le.mp h393).le h399
    · -- right
      exact CKLaneC2R.Cells.S05.B022.c449_pos (not_le.mp h271).le h377 (not_le.mp h399).le h398
  · -- right
    by_cases h400 : z ≤ ((123307/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B022.c452_pos (not_le.mp h271).le h377 (not_le.mp h398).le h400
    · -- right
      exact CKLaneC2R.Cells.S05.B022.c453_pos (not_le.mp h271).le h377 (not_le.mp h400).le h397

end CKLaneC2R.CompactCover


