-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g18
-- name    : CK_CKLaneC2R_CompactCover_S02_g18
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T01:57:06.541921+00:00
-- url     : https://prove2.me/theorems/472ce09f-0289-4f1f-b051-180dc256d964
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B032
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B033
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B019

namespace CKLaneC2R.CompactCover

theorem strip2_s028 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : a ≤ ((3/8 : ℚ) : ℝ)) (h316 : a ≤ ((29/80 : ℚ) : ℝ)) (h317 : z ≤ ((217/400 : ℚ) : ℝ)) (h318 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h319 : a ≤ ((57/160 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h320 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h321 : z ≤ ((2289/16000 : ℚ) : ℝ)
    · -- left
      by_cases h322 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h323 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B031.c635_pos (not_le.mp h1).le h319 hz1 h323
        · -- right
          exact CKLaneC2R.Cells.S02.B031.c637_pos (not_le.mp h1).le h319 (not_le.mp h323).le h322
      · -- right
        by_cases h324 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B032.c643_pos (not_le.mp h1).le h319 (not_le.mp h322).le h324
        · -- right
          exact CKLaneC2R.Cells.S02.B032.c645_pos (not_le.mp h1).le h319 (not_le.mp h324).le h321
    · -- right
      by_cases h325 : z ≤ ((5491/32000 : ℚ) : ℝ)
      · -- left
        by_cases h326 : z ≤ ((10069/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B033.c667_pos (not_le.mp h1).le h319 (not_le.mp h321).le h326
        · -- right
          exact CKLaneC2R.Cells.S02.B033.c669_pos (not_le.mp h1).le h319 (not_le.mp h326).le h325
      · -- right
        exact CKLaneC2R.Cells.S02.B018.c370_pos (not_le.mp h1).le h319 (not_le.mp h325).le h320
  · -- right
    by_cases h327 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h328 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B019.c381_pos (not_le.mp h1).le h319 (not_le.mp h320).le h328
      · -- right
        exact CKLaneC2R.Cells.S02.B019.c383_pos (not_le.mp h1).le h319 (not_le.mp h328).le h327
    · -- right
      by_cases h329 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B019.c389_pos (not_le.mp h1).le h319 (not_le.mp h327).le h329
      · -- right
        exact CKLaneC2R.Cells.S02.B019.c391_pos (not_le.mp h1).le h319 (not_le.mp h329).le h318

theorem strip2_s029 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : a ≤ ((3/8 : ℚ) : ℝ)) (h316 : a ≤ ((29/80 : ℚ) : ℝ)) (h317 : z ≤ ((217/400 : ℚ) : ℝ)) (h318 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h319 : ¬ (a ≤ ((57/160 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h330 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h331 : z ≤ ((2289/16000 : ℚ) : ℝ)
    · -- left
      by_cases h332 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h333 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B031.c636_pos (not_le.mp h319).le h316 hz1 h333
        · -- right
          exact CKLaneC2R.Cells.S02.B031.c638_pos (not_le.mp h319).le h316 (not_le.mp h333).le h332
      · -- right
        by_cases h334 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B032.c644_pos (not_le.mp h319).le h316 (not_le.mp h332).le h334
        · -- right
          exact CKLaneC2R.Cells.S02.B032.c646_pos (not_le.mp h319).le h316 (not_le.mp h334).le h331
    · -- right
      by_cases h335 : z ≤ ((5491/32000 : ℚ) : ℝ)
      · -- left
        by_cases h336 : z ≤ ((10069/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B033.c668_pos (not_le.mp h319).le h316 (not_le.mp h331).le h336
        · -- right
          exact CKLaneC2R.Cells.S02.B033.c670_pos (not_le.mp h319).le h316 (not_le.mp h336).le h335
      · -- right
        exact CKLaneC2R.Cells.S02.B018.c371_pos (not_le.mp h319).le h316 (not_le.mp h335).le h330
  · -- right
    by_cases h337 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h338 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B019.c382_pos (not_le.mp h319).le h316 (not_le.mp h330).le h338
      · -- right
        exact CKLaneC2R.Cells.S02.B019.c384_pos (not_le.mp h319).le h316 (not_le.mp h338).le h337
    · -- right
      by_cases h339 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B019.c390_pos (not_le.mp h319).le h316 (not_le.mp h337).le h339
      · -- right
        exact CKLaneC2R.Cells.S02.B019.c392_pos (not_le.mp h319).le h316 (not_le.mp h339).le h318

end CKLaneC2R.CompactCover


