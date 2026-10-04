-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g18
-- name    : CK_CKLaneC2R_CompactCover_S03_g18
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T04:56:27.43215+00:00
-- url     : https://prove2.me/theorems/95d1ae8e-939e-48f5-8b33-cd704a0f75e7
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

import Definitions.Def_CK_CKLaneC2R_Cells_S03_B007
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B019

namespace CKLaneC2R.CompactCover

theorem strip3_s026 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((3/5 : ℚ) : ℝ))) (h220 : a ≤ ((13/20 : ℚ) : ℝ)) (h221 : ¬ (a ≤ ((5/8 : ℚ) : ℝ))) (h268 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h290 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h298 : z ≤ ((7079/8000 : ℚ) : ℝ)
  · -- left
    by_cases h299 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h300 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B007.c158_pos (not_le.mp h221).le h220 (not_le.mp h290).le h300
      · -- right
        exact CKLaneC2R.Cells.S03.B007.c159_pos (not_le.mp h221).le h220 (not_le.mp h300).le h299
    · -- right
      by_cases h301 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B008.c162_pos (not_le.mp h221).le h220 (not_le.mp h299).le h301
      · -- right
        exact CKLaneC2R.Cells.S03.B008.c163_pos (not_le.mp h221).le h220 (not_le.mp h301).le h298
  · -- right
    by_cases h302 : z ≤ ((15071/16000 : ℚ) : ℝ)
    · -- left
      by_cases h303 : a ≤ ((51/80 : ℚ) : ℝ)
      · -- left
        by_cases h304 : z ≤ ((29229/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B013.c278_pos (not_le.mp h221).le h303 (not_le.mp h298).le h304
        · -- right
          exact CKLaneC2R.Cells.S03.B014.c280_pos (not_le.mp h221).le h303 (not_le.mp h304).le h302
      · -- right
        by_cases h305 : z ≤ ((29229/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B013.c279_pos (not_le.mp h303).le h220 (not_le.mp h298).le h305
        · -- right
          exact CKLaneC2R.Cells.S03.B014.c281_pos (not_le.mp h303).le h220 (not_le.mp h305).le h302
    · -- right
      by_cases h306 : z ≤ ((6211/6400 : ℚ) : ℝ)
      · -- left
        by_cases h307 : z ≤ ((61197/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B014.c296_pos (not_le.mp h221).le h220 (not_le.mp h302).le h307
        · -- right
          exact CKLaneC2R.Cells.S03.B014.c297_pos (not_le.mp h221).le h220 (not_le.mp h307).le h306
      · -- right
        by_cases h308 : z ≤ ((63023/64000 : ℚ) : ℝ)
        · -- left
          by_cases h309 : a ≤ ((51/80 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B017.c356_pos (not_le.mp h221).le h309 (not_le.mp h306).le h308
          · -- right
            exact CKLaneC2R.Cells.S03.B017.c357_pos (not_le.mp h309).le h220 (not_le.mp h306).le h308
        · -- right
          by_cases h310 : z ≤ ((126959/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B018.c364_pos (not_le.mp h221).le h220 (not_le.mp h308).le h310
          · -- right
            by_cases h311 : z ≤ ((254831/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S03.B018.c378_pos (not_le.mp h221).le h220 (not_le.mp h310).le h311
            · -- right
              by_cases h312 : z ≤ ((20423/20480 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S03.B019.c386_pos (not_le.mp h221).le h220 (not_le.mp h311).le h312
              · -- right
                exact CKLaneC2R.Cells.S03.B019.c388_pos (not_le.mp h221).le h220 (not_le.mp h312).le hz2

end CKLaneC2R.CompactCover


