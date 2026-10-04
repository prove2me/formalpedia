-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g24
-- name    : CK_CKLaneC2R_CompactCover_S03_g24
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T11:12:39.055754+00:00
-- url     : https://prove2.me/theorems/091d6f68-2e20-420a-9df6-794ffe091a4a
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
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B015
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B019

namespace CKLaneC2R.CompactCover

theorem strip3_s034 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((3/5 : ℚ) : ℝ))) (h220 : ¬ (a ≤ ((13/20 : ℚ) : ℝ))) (h313 : ¬ (a ≤ ((27/40 : ℚ) : ℝ))) (h357 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h377 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h385 : z ≤ ((7079/8000 : ℚ) : ℝ)
  · -- left
    by_cases h386 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h387 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B008.c166_pos (not_le.mp h313).le ha2 (not_le.mp h377).le h387
      · -- right
        exact CKLaneC2R.Cells.S03.B008.c167_pos (not_le.mp h313).le ha2 (not_le.mp h387).le h386
    · -- right
      by_cases h388 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B008.c170_pos (not_le.mp h313).le ha2 (not_le.mp h386).le h388
      · -- right
        exact CKLaneC2R.Cells.S03.B008.c171_pos (not_le.mp h313).le ha2 (not_le.mp h388).le h385
  · -- right
    by_cases h389 : z ≤ ((15071/16000 : ℚ) : ℝ)
    · -- left
      by_cases h390 : a ≤ ((11/16 : ℚ) : ℝ)
      · -- left
        by_cases h391 : z ≤ ((29229/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B014.c286_pos (not_le.mp h313).le h390 (not_le.mp h385).le h391
        · -- right
          exact CKLaneC2R.Cells.S03.B014.c288_pos (not_le.mp h313).le h390 (not_le.mp h391).le h389
      · -- right
        by_cases h392 : z ≤ ((29229/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B014.c287_pos (not_le.mp h390).le ha2 (not_le.mp h385).le h392
        · -- right
          exact CKLaneC2R.Cells.S03.B014.c289_pos (not_le.mp h390).le ha2 (not_le.mp h392).le h389
    · -- right
      by_cases h393 : z ≤ ((6211/6400 : ℚ) : ℝ)
      · -- left
        by_cases h394 : z ≤ ((61197/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B015.c300_pos (not_le.mp h313).le ha2 (not_le.mp h389).le h394
        · -- right
          exact CKLaneC2R.Cells.S03.B015.c301_pos (not_le.mp h313).le ha2 (not_le.mp h394).le h393
      · -- right
        by_cases h395 : z ≤ ((63023/64000 : ℚ) : ℝ)
        · -- left
          by_cases h396 : a ≤ ((11/16 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B018.c360_pos (not_le.mp h313).le h396 (not_le.mp h393).le h395
          · -- right
            exact CKLaneC2R.Cells.S03.B018.c361_pos (not_le.mp h396).le ha2 (not_le.mp h393).le h395
        · -- right
          by_cases h397 : z ≤ ((126959/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B018.c366_pos (not_le.mp h313).le ha2 (not_le.mp h395).le h397
          · -- right
            by_cases h398 : z ≤ ((254831/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S03.B019.c380_pos (not_le.mp h313).le ha2 (not_le.mp h397).le h398
            · -- right
              by_cases h399 : z ≤ ((20423/20480 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S03.B019.c391_pos (not_le.mp h313).le ha2 (not_le.mp h398).le h399
              · -- right
                exact CKLaneC2R.Cells.S03.B019.c392_pos (not_le.mp h313).le ha2 (not_le.mp h399).le hz2

end CKLaneC2R.CompactCover


