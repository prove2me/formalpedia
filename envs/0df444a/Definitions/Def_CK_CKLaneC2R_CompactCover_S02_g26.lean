-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g26
-- name    : CK_CKLaneC2R_CompactCover_S02_g26
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T18:58:34.718122+00:00
-- url     : https://prove2.me/theorems/5c24a239-ee8b-4fe9-aa8e-30b6aeafb4cd
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B032
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B033
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B018

namespace CKLaneC2R.CompactCover

theorem strip2_s040 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : ¬ (a ≤ ((3/8 : ℚ) : ℝ))) (h430 : a ≤ ((31/80 : ℚ) : ℝ)) (h431 : z ≤ ((217/400 : ℚ) : ℝ)) (h432 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h433 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h434 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h435 : a ≤ ((61/160 : ℚ) : ℝ)
    · -- left
      by_cases h436 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h437 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B032.c651_pos (not_le.mp h315).le h435 hz1 h437
        · -- right
          exact CKLaneC2R.Cells.S02.B032.c653_pos (not_le.mp h315).le h435 (not_le.mp h437).le h436
      · -- right
        by_cases h438 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B032.c659_pos (not_le.mp h315).le h435 (not_le.mp h436).le h438
        · -- right
          exact CKLaneC2R.Cells.S02.B033.c661_pos (not_le.mp h315).le h435 (not_le.mp h438).le h434
    · -- right
      by_cases h439 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h440 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B032.c652_pos (not_le.mp h435).le h430 hz1 h440
        · -- right
          exact CKLaneC2R.Cells.S02.B032.c654_pos (not_le.mp h435).le h430 (not_le.mp h440).le h439
      · -- right
        by_cases h441 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B033.c660_pos (not_le.mp h435).le h430 (not_le.mp h439).le h441
        · -- right
          exact CKLaneC2R.Cells.S02.B033.c662_pos (not_le.mp h435).le h430 (not_le.mp h441).le h434
  · -- right
    by_cases h442 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h443 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        by_cases h444 : a ≤ ((61/160 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B033.c675_pos (not_le.mp h315).le h444 (not_le.mp h434).le h443
        · -- right
          exact CKLaneC2R.Cells.S02.B033.c676_pos (not_le.mp h444).le h430 (not_le.mp h434).le h443
      · -- right
        exact CKLaneC2R.Cells.S02.B018.c374_pos (not_le.mp h315).le h430 (not_le.mp h443).le h442
    · -- right
      by_cases h445 : a ≤ ((61/160 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B018.c377_pos (not_le.mp h315).le h445 (not_le.mp h442).le h433
      · -- right
        exact CKLaneC2R.Cells.S02.B018.c378_pos (not_le.mp h445).le h430 (not_le.mp h442).le h433

end CKLaneC2R.CompactCover


