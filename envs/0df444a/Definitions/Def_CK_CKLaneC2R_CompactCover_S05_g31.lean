-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g31
-- name    : CK_CKLaneC2R_CompactCover_S05_g31
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T07:38:38.250635+00:00
-- url     : https://prove2.me/theorems/088ece67-5e27-4b60-bee1-a6822438ef4a
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B026
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B028
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B029
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B030
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B031

namespace CKLaneC2R.CompactCover

theorem strip5_s057 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : a ≤ ((3177/3200 : ℚ) : ℝ)) (h377 : a ≤ ((31671/32000 : ℚ) : ℝ)) (h378 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h385 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h389 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h393 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h397 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) (h401 : a ≤ ((63243/64000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h402 : z ≤ ((63023/64000 : ℚ) : ℝ)
  · -- left
    by_cases h403 : z ≤ ((125133/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B026.c521_pos (not_le.mp h271).le h401 (not_le.mp h397).le h403
    · -- right
      exact CKLaneC2R.Cells.S05.B026.c525_pos (not_le.mp h271).le h401 (not_le.mp h403).le h402
  · -- right
    by_cases h404 : z ≤ ((126959/128000 : ℚ) : ℝ)
    · -- left
      by_cases h405 : z ≤ ((50601/51200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B028.c574_pos (not_le.mp h271).le h401 (not_le.mp h402).le h405
      · -- right
        exact CKLaneC2R.Cells.S05.B028.c576_pos (not_le.mp h271).le h401 (not_le.mp h405).le h404
    · -- right
      by_cases h406 : z ≤ ((254831/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B029.c581_pos (not_le.mp h271).le h401 (not_le.mp h404).le h406
      · -- right
        by_cases h407 : z ≤ ((20423/20480 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B030.c608_pos (not_le.mp h271).le h401 (not_le.mp h406).le h407
        · -- right
          exact CKLaneC2R.Cells.S05.B030.c609_pos (not_le.mp h271).le h401 (not_le.mp h407).le hz2

theorem strip5_s058 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : a ≤ ((3177/3200 : ℚ) : ℝ)) (h377 : a ≤ ((31671/32000 : ℚ) : ℝ)) (h378 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h385 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h389 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h393 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h397 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) (h401 : ¬ (a ≤ ((63243/64000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h408 : z ≤ ((63023/64000 : ℚ) : ℝ)
  · -- left
    by_cases h409 : z ≤ ((125133/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B026.c522_pos (not_le.mp h401).le h377 (not_le.mp h397).le h409
    · -- right
      exact CKLaneC2R.Cells.S05.B026.c526_pos (not_le.mp h401).le h377 (not_le.mp h409).le h408
  · -- right
    by_cases h410 : z ≤ ((126959/128000 : ℚ) : ℝ)
    · -- left
      by_cases h411 : z ≤ ((50601/51200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B028.c575_pos (not_le.mp h401).le h377 (not_le.mp h408).le h411
      · -- right
        exact CKLaneC2R.Cells.S05.B028.c577_pos (not_le.mp h401).le h377 (not_le.mp h411).le h410
    · -- right
      by_cases h412 : z ≤ ((254831/256000 : ℚ) : ℝ)
      · -- left
        by_cases h413 : z ≤ ((508749/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B030.c606_pos (not_le.mp h401).le h377 (not_le.mp h410).le h413
        · -- right
          exact CKLaneC2R.Cells.S05.B030.c607_pos (not_le.mp h401).le h377 (not_le.mp h413).le h412
      · -- right
        by_cases h414 : z ≤ ((20423/20480 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B030.c610_pos (not_le.mp h401).le h377 (not_le.mp h412).le h414
        · -- right
          by_cases h415 : a ≤ ((25317/25600 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B031.c628_pos (not_le.mp h401).le h415 (not_le.mp h414).le hz2
          · -- right
            exact CKLaneC2R.Cells.S05.B031.c629_pos (not_le.mp h415).le h377 (not_le.mp h414).le hz2

end CKLaneC2R.CompactCover


