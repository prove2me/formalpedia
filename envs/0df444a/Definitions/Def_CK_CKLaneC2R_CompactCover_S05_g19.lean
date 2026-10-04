-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g19
-- name    : CK_CKLaneC2R_CompactCover_S05_g19
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T06:09:57.523723+00:00
-- url     : https://prove2.me/theorems/67fc1f1f-461a-46b4-845f-2eb89f2218e8
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B021
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B024
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B026

namespace CKLaneC2R.CompactCover

theorem strip5_s033 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : a ≤ ((3897/4000 : ℚ) : ℝ)) (h148 : ¬ (a ≤ ((1539/1600 : ℚ) : ℝ))) (h199 : ¬ (a ≤ ((15489/16000 : ℚ) : ℝ))) (h235 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h243 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h247 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h251 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h255 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h256 : z ≤ ((61197/64000 : ℚ) : ℝ)
  · -- left
    by_cases h257 : a ≤ ((31077/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B018.c363_pos (not_le.mp h199).le h257 (not_le.mp h251).le h256
    · -- right
      exact CKLaneC2R.Cells.S05.B018.c364_pos (not_le.mp h257).le h147 (not_le.mp h251).le h256
  · -- right
    by_cases h258 : z ≤ ((123307/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B018.c367_pos (not_le.mp h199).le h147 (not_le.mp h256).le h258
    · -- right
      by_cases h259 : a ≤ ((31077/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B020.c419_pos (not_le.mp h199).le h259 (not_le.mp h258).le h255
      · -- right
        exact CKLaneC2R.Cells.S05.B021.c420_pos (not_le.mp h259).le h147 (not_le.mp h258).le h255

theorem strip5_s034 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : a ≤ ((3897/4000 : ℚ) : ℝ)) (h148 : ¬ (a ≤ ((1539/1600 : ℚ) : ℝ))) (h199 : ¬ (a ≤ ((15489/16000 : ℚ) : ℝ))) (h235 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h243 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h247 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h251 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h255 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h260 : a ≤ ((31077/32000 : ℚ) : ℝ)
  · -- left
    by_cases h261 : z ≤ ((63023/64000 : ℚ) : ℝ)
    · -- left
      by_cases h262 : z ≤ ((125133/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B021.c427_pos (not_le.mp h199).le h260 (not_le.mp h255).le h262
      · -- right
        exact CKLaneC2R.Cells.S05.B021.c429_pos (not_le.mp h199).le h260 (not_le.mp h262).le h261
    · -- right
      by_cases h263 : z ≤ ((126959/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B021.c438_pos (not_le.mp h199).le h260 (not_le.mp h261).le h263
      · -- right
        by_cases h264 : z ≤ ((254831/256000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B024.c497_pos (not_le.mp h199).le h260 (not_le.mp h263).le h264
        · -- right
          by_cases h265 : z ≤ ((20423/20480 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B026.c532_pos (not_le.mp h199).le h260 (not_le.mp h264).le h265
          · -- right
            exact CKLaneC2R.Cells.S05.B026.c533_pos (not_le.mp h199).le h260 (not_le.mp h265).le hz2
  · -- right
    by_cases h266 : z ≤ ((63023/64000 : ℚ) : ℝ)
    · -- left
      by_cases h267 : z ≤ ((125133/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B021.c428_pos (not_le.mp h260).le h147 (not_le.mp h255).le h267
      · -- right
        exact CKLaneC2R.Cells.S05.B021.c430_pos (not_le.mp h260).le h147 (not_le.mp h267).le h266
    · -- right
      by_cases h268 : z ≤ ((126959/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B021.c439_pos (not_le.mp h260).le h147 (not_le.mp h266).le h268
      · -- right
        by_cases h269 : z ≤ ((254831/256000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B024.c498_pos (not_le.mp h260).le h147 (not_le.mp h268).le h269
        · -- right
          by_cases h270 : z ≤ ((20423/20480 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B026.c534_pos (not_le.mp h260).le h147 (not_le.mp h269).le h270
          · -- right
            exact CKLaneC2R.Cells.S05.B026.c535_pos (not_le.mp h260).le h147 (not_le.mp h270).le hz2

end CKLaneC2R.CompactCover


