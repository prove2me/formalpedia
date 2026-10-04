-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g21
-- name    : CK_CKLaneC2R_CompactCover_S03_g21
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T10:12:10.02139+00:00
-- url     : https://prove2.me/theorems/e9e9b850-28c5-4724-96d8-2addda31fe3f
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S03 (proof part of strip3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S03 (proof part of strip3).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S03_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B019

namespace CKLaneC2R.CompactCover

theorem strip3_s030 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((3/5 : ℚ) : ℝ))) (h220 : ¬ (a ≤ ((13/20 : ℚ) : ℝ))) (h313 : a ≤ ((27/40 : ℚ) : ℝ)) (h314 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h334 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h342 : z ≤ ((7079/8000 : ℚ) : ℝ)
  · -- left
    by_cases h343 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h344 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B008.c164_pos (not_le.mp h220).le h313 (not_le.mp h334).le h344
      · -- right
        exact CKLaneC2R.Cells.S03.B008.c165_pos (not_le.mp h220).le h313 (not_le.mp h344).le h343
    · -- right
      by_cases h345 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B008.c168_pos (not_le.mp h220).le h313 (not_le.mp h343).le h345
      · -- right
        exact CKLaneC2R.Cells.S03.B008.c169_pos (not_le.mp h220).le h313 (not_le.mp h345).le h342
  · -- right
    by_cases h346 : z ≤ ((15071/16000 : ℚ) : ℝ)
    · -- left
      by_cases h347 : a ≤ ((53/80 : ℚ) : ℝ)
      · -- left
        by_cases h348 : z ≤ ((29229/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B014.c282_pos (not_le.mp h220).le h347 (not_le.mp h342).le h348
        · -- right
          exact CKLaneC2R.Cells.S03.B014.c284_pos (not_le.mp h220).le h347 (not_le.mp h348).le h346
      · -- right
        by_cases h349 : z ≤ ((29229/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B014.c283_pos (not_le.mp h347).le h313 (not_le.mp h342).le h349
        · -- right
          exact CKLaneC2R.Cells.S03.B014.c285_pos (not_le.mp h347).le h313 (not_le.mp h349).le h346
    · -- right
      by_cases h350 : z ≤ ((6211/6400 : ℚ) : ℝ)
      · -- left
        by_cases h351 : z ≤ ((61197/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B014.c298_pos (not_le.mp h220).le h313 (not_le.mp h346).le h351
        · -- right
          exact CKLaneC2R.Cells.S03.B014.c299_pos (not_le.mp h220).le h313 (not_le.mp h351).le h350
      · -- right
        by_cases h352 : z ≤ ((63023/64000 : ℚ) : ℝ)
        · -- left
          by_cases h353 : a ≤ ((53/80 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B017.c358_pos (not_le.mp h220).le h353 (not_le.mp h350).le h352
          · -- right
            exact CKLaneC2R.Cells.S03.B017.c359_pos (not_le.mp h353).le h313 (not_le.mp h350).le h352
        · -- right
          by_cases h354 : z ≤ ((126959/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B018.c365_pos (not_le.mp h220).le h313 (not_le.mp h352).le h354
          · -- right
            by_cases h355 : z ≤ ((254831/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S03.B018.c379_pos (not_le.mp h220).le h313 (not_le.mp h354).le h355
            · -- right
              by_cases h356 : z ≤ ((20423/20480 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S03.B019.c389_pos (not_le.mp h220).le h313 (not_le.mp h355).le h356
              · -- right
                exact CKLaneC2R.Cells.S03.B019.c390_pos (not_le.mp h220).le h313 (not_le.mp h356).le hz2

end CKLaneC2R.CompactCover


