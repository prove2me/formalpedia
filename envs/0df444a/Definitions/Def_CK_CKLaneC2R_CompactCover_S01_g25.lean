-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g25
-- name    : CK_CKLaneC2R_CompactCover_S01_g25
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T09:55:43.694023+00:00
-- url     : https://prove2.me/theorems/202e598f-8622-4430-bff5-8dcb87401fef
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S01 (proof part of strip1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S01 (proof part of strip1).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B049
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B050
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B032
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B033

namespace CKLaneC2R.CompactCover

theorem strip1_s032 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((17/80 : ℚ) : ℝ))) (h224 : ¬ (a ≤ ((7/32 : ℚ) : ℝ))) (h324 : z ≤ ((217/400 : ℚ) : ℝ)) (h325 : a ≤ ((71/320 : ℚ) : ℝ)) (h326 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h327 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h328 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h329 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h330 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h331 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B049.c988_pos (not_le.mp h224).le h325 hz1 h331
        · -- right
          exact CKLaneC2R.Cells.S01.B049.c990_pos (not_le.mp h224).le h325 (not_le.mp h331).le h330
      · -- right
        by_cases h332 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B049.c992_pos (not_le.mp h224).le h325 (not_le.mp h330).le h332
        · -- right
          exact CKLaneC2R.Cells.S01.B049.c993_pos (not_le.mp h224).le h325 (not_le.mp h332).le h329
    · -- right
      by_cases h333 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h334 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B050.c1004_pos (not_le.mp h224).le h325 (not_le.mp h329).le h334
        · -- right
          exact CKLaneC2R.Cells.S01.B050.c1005_pos (not_le.mp h224).le h325 (not_le.mp h334).le h333
      · -- right
        exact CKLaneC2R.Cells.S01.B031.c632_pos (not_le.mp h224).le h325 (not_le.mp h333).le h328
  · -- right
    by_cases h335 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h336 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B032.c651_pos (not_le.mp h224).le h325 (not_le.mp h328).le h336
      · -- right
        exact CKLaneC2R.Cells.S01.B032.c653_pos (not_le.mp h224).le h325 (not_le.mp h336).le h335
    · -- right
      by_cases h337 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B032.c659_pos (not_le.mp h224).le h325 (not_le.mp h335).le h337
      · -- right
        exact CKLaneC2R.Cells.S01.B033.c661_pos (not_le.mp h224).le h325 (not_le.mp h337).le h327

end CKLaneC2R.CompactCover


