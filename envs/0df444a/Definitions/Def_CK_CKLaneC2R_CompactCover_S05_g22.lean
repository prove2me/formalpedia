-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g22
-- name    : CK_CKLaneC2R_CompactCover_S05_g22
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T19:52:13.78626+00:00
-- url     : https://prove2.me/theorems/f6a73769-2229-46cb-8bc9-61ea8251a43b
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
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B022
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B025
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B027

namespace CKLaneC2R.CompactCover

theorem strip5_s039 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : a ≤ ((7893/8000 : ℚ) : ℝ)) (h272 : a ≤ ((15687/16000 : ℚ) : ℝ)) (h273 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h282 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h286 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h291 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h296 : a ≤ ((1251/1280 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h297 : z ≤ ((6211/6400 : ℚ) : ℝ)
  · -- left
    by_cases h298 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B018.c371_pos (not_le.mp h147).le h296 (not_le.mp h291).le h298
    · -- right
      by_cases h299 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B022.c440_pos (not_le.mp h147).le h296 (not_le.mp h298).le h299
      · -- right
        exact CKLaneC2R.Cells.S05.B022.c441_pos (not_le.mp h147).le h296 (not_le.mp h299).le h297
  · -- right
    by_cases h300 : z ≤ ((63023/64000 : ℚ) : ℝ)
    · -- left
      by_cases h301 : z ≤ ((125133/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B022.c455_pos (not_le.mp h147).le h296 (not_le.mp h297).le h301
      · -- right
        exact CKLaneC2R.Cells.S05.B022.c457_pos (not_le.mp h147).le h296 (not_le.mp h301).le h300
    · -- right
      by_cases h302 : z ≤ ((126959/128000 : ℚ) : ℝ)
      · -- left
        by_cases h303 : z ≤ ((50601/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B025.c515_pos (not_le.mp h147).le h296 (not_le.mp h300).le h303
        · -- right
          exact CKLaneC2R.Cells.S05.B025.c516_pos (not_le.mp h147).le h296 (not_le.mp h303).le h302
      · -- right
        by_cases h304 : z ≤ ((254831/256000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B025.c519_pos (not_le.mp h147).le h296 (not_le.mp h302).le h304
        · -- right
          by_cases h305 : z ≤ ((20423/20480 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B027.c549_pos (not_le.mp h147).le h296 (not_le.mp h304).le h305
          · -- right
            exact CKLaneC2R.Cells.S05.B027.c550_pos (not_le.mp h147).le h296 (not_le.mp h305).le hz2

theorem strip5_s040 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : a ≤ ((7893/8000 : ℚ) : ℝ)) (h272 : a ≤ ((15687/16000 : ℚ) : ℝ)) (h273 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h282 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h286 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h291 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h296 : ¬ (a ≤ ((1251/1280 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h306 : z ≤ ((6211/6400 : ℚ) : ℝ)
  · -- left
    by_cases h307 : z ≤ ((61197/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B018.c372_pos (not_le.mp h296).le h272 (not_le.mp h291).le h307
    · -- right
      by_cases h308 : z ≤ ((123307/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B022.c442_pos (not_le.mp h296).le h272 (not_le.mp h307).le h308
      · -- right
        exact CKLaneC2R.Cells.S05.B022.c443_pos (not_le.mp h296).le h272 (not_le.mp h308).le h306
  · -- right
    by_cases h309 : z ≤ ((63023/64000 : ℚ) : ℝ)
    · -- left
      by_cases h310 : z ≤ ((125133/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B022.c456_pos (not_le.mp h296).le h272 (not_le.mp h306).le h310
      · -- right
        exact CKLaneC2R.Cells.S05.B022.c458_pos (not_le.mp h296).le h272 (not_le.mp h310).le h309
    · -- right
      by_cases h311 : z ≤ ((126959/128000 : ℚ) : ℝ)
      · -- left
        by_cases h312 : z ≤ ((50601/51200 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B025.c517_pos (not_le.mp h296).le h272 (not_le.mp h309).le h312
        · -- right
          exact CKLaneC2R.Cells.S05.B025.c518_pos (not_le.mp h296).le h272 (not_le.mp h312).le h311
      · -- right
        by_cases h313 : z ≤ ((254831/256000 : ℚ) : ℝ)
        · -- left
          by_cases h314 : a ≤ ((62649/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B027.c547_pos (not_le.mp h296).le h314 (not_le.mp h311).le h313
          · -- right
            exact CKLaneC2R.Cells.S05.B027.c548_pos (not_le.mp h314).le h272 (not_le.mp h311).le h313
        · -- right
          by_cases h315 : z ≤ ((20423/20480 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B027.c551_pos (not_le.mp h296).le h272 (not_le.mp h313).le h315
          · -- right
            exact CKLaneC2R.Cells.S05.B027.c552_pos (not_le.mp h296).le h272 (not_le.mp h315).le hz2

end CKLaneC2R.CompactCover


