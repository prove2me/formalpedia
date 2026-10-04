-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g25
-- name    : CK_CKLaneC2R_CompactCover_S02_g25
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T15:41:06.84012+00:00
-- url     : https://prove2.me/theorems/af7c7e97-4098-4ef1-a4c7-bff3d9151ec5
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S02 (proof part of strip2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S02 (proof part of strip2).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B026
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B036
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B039
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B040
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B041
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B042

namespace CKLaneC2R.CompactCover

theorem strip2_s039 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : a ≤ ((3/8 : ℚ) : ℝ)) (h316 : ¬ (a ≤ ((29/80 : ℚ) : ℝ))) (h375 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h405 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h413 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h417 : z ≤ ((15071/16000 : ℚ) : ℝ)
  · -- left
    by_cases h418 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      by_cases h419 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B026.c535_pos (not_le.mp h316).le h315 (not_le.mp h413).le h419
      · -- right
        exact CKLaneC2R.Cells.S02.B026.c536_pos (not_le.mp h316).le h315 (not_le.mp h419).le h418
    · -- right
      by_cases h420 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B026.c539_pos (not_le.mp h316).le h315 (not_le.mp h418).le h420
      · -- right
        exact CKLaneC2R.Cells.S02.B027.c540_pos (not_le.mp h316).le h315 (not_le.mp h420).le h417
  · -- right
    by_cases h421 : z ≤ ((6211/6400 : ℚ) : ℝ)
    · -- left
      by_cases h422 : z ≤ ((61197/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B027.c557_pos (not_le.mp h316).le h315 (not_le.mp h417).le h422
      · -- right
        exact CKLaneC2R.Cells.S02.B027.c558_pos (not_le.mp h316).le h315 (not_le.mp h422).le h421
    · -- right
      by_cases h423 : z ≤ ((63023/64000 : ℚ) : ℝ)
      · -- left
        by_cases h424 : z ≤ ((125133/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B036.c725_pos (not_le.mp h316).le h315 (not_le.mp h421).le h424
        · -- right
          exact CKLaneC2R.Cells.S02.B036.c726_pos (not_le.mp h316).le h315 (not_le.mp h424).le h423
      · -- right
        by_cases h425 : z ≤ ((126959/128000 : ℚ) : ℝ)
        · -- left
          by_cases h426 : z ≤ ((50601/51200 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B039.c793_pos (not_le.mp h316).le h315 (not_le.mp h423).le h426
          · -- right
            exact CKLaneC2R.Cells.S02.B039.c794_pos (not_le.mp h316).le h315 (not_le.mp h426).le h425
        · -- right
          by_cases h427 : z ≤ ((254831/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B040.c802_pos (not_le.mp h316).le h315 (not_le.mp h425).le h427
          · -- right
            by_cases h428 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S02.B041.c823_pos (not_le.mp h316).le h315 (not_le.mp h427).le h428
            · -- right
              by_cases h429 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S02.B042.c848_pos (not_le.mp h316).le h315 (not_le.mp h428).le h429
              · -- right
                exact CKLaneC2R.Cells.S02.B042.c849_pos (not_le.mp h316).le h315 (not_le.mp h429).le hz2

end CKLaneC2R.CompactCover


