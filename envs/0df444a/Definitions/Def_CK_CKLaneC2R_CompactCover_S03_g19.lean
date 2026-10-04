-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g19
-- name    : CK_CKLaneC2R_CompactCover_S03_g19
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T05:47:36.804969+00:00
-- url     : https://prove2.me/theorems/1dcb540b-497d-4c95-a2a5-7329656613fb
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

import Definitions.Def_CK_CKLaneC2R_Cells_S03_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B011
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B001
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B002
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B003

namespace CKLaneC2R.CompactCover

theorem strip3_s027 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((3/5 : ℚ) : ℝ))) (h220 : ¬ (a ≤ ((13/20 : ℚ) : ℝ))) (h313 : a ≤ ((27/40 : ℚ) : ℝ)) (h314 : z ≤ ((217/400 : ℚ) : ℝ)) (h315 : z ≤ ((1257/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h316 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h317 : z ≤ ((2289/16000 : ℚ) : ℝ)
    · -- left
      by_cases h318 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h319 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          by_cases h320 : a ≤ ((53/80 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B016.c334_pos (not_le.mp h220).le h320 hz1 h319
          · -- right
            exact CKLaneC2R.Cells.S03.B016.c335_pos (not_le.mp h320).le h313 hz1 h319
        · -- right
          exact CKLaneC2R.Cells.S03.B011.c232_pos (not_le.mp h220).le h313 (not_le.mp h319).le h318
      · -- right
        by_cases h321 : a ≤ ((53/80 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B011.c233_pos (not_le.mp h220).le h321 (not_le.mp h318).le h317
        · -- right
          exact CKLaneC2R.Cells.S03.B011.c234_pos (not_le.mp h321).le h313 (not_le.mp h318).le h317
    · -- right
      by_cases h322 : z ≤ ((5491/32000 : ℚ) : ℝ)
      · -- left
        by_cases h323 : a ≤ ((53/80 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B011.c238_pos (not_le.mp h220).le h323 (not_le.mp h317).le h322
        · -- right
          exact CKLaneC2R.Cells.S03.B011.c239_pos (not_le.mp h323).le h313 (not_le.mp h317).le h322
      · -- right
        exact CKLaneC2R.Cells.S03.B001.c34_pos (not_le.mp h220).le h313 (not_le.mp h322).le h316
  · -- right
    by_cases h324 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h325 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B002.c43_pos (not_le.mp h220).le h313 (not_le.mp h316).le h325
      · -- right
        exact CKLaneC2R.Cells.S03.B002.c44_pos (not_le.mp h220).le h313 (not_le.mp h325).le h324
    · -- right
      by_cases h326 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B002.c47_pos (not_le.mp h220).le h313 (not_le.mp h324).le h326
      · -- right
        exact CKLaneC2R.Cells.S03.B002.c48_pos (not_le.mp h220).le h313 (not_le.mp h326).le h315

theorem strip3_s028 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((3/5 : ℚ) : ℝ))) (h220 : ¬ (a ≤ ((13/20 : ℚ) : ℝ))) (h313 : a ≤ ((27/40 : ℚ) : ℝ)) (h314 : z ≤ ((217/400 : ℚ) : ℝ)) (h315 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h327 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h328 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h329 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B003.c67_pos (not_le.mp h220).le h313 (not_le.mp h315).le h329
      · -- right
        exact CKLaneC2R.Cells.S03.B003.c68_pos (not_le.mp h220).le h313 (not_le.mp h329).le h328
    · -- right
      by_cases h330 : a ≤ ((53/80 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B003.c69_pos (not_le.mp h220).le h330 (not_le.mp h328).le h327
      · -- right
        exact CKLaneC2R.Cells.S03.B003.c70_pos (not_le.mp h330).le h313 (not_le.mp h328).le h327
  · -- right
    by_cases h331 : a ≤ ((53/80 : ℚ) : ℝ)
    · -- left
      by_cases h332 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B003.c75_pos (not_le.mp h220).le h331 (not_le.mp h327).le h332
      · -- right
        exact CKLaneC2R.Cells.S03.B003.c77_pos (not_le.mp h220).le h331 (not_le.mp h332).le h314
    · -- right
      by_cases h333 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B003.c76_pos (not_le.mp h331).le h313 (not_le.mp h327).le h333
      · -- right
        exact CKLaneC2R.Cells.S03.B003.c78_pos (not_le.mp h331).le h313 (not_le.mp h333).le h314

end CKLaneC2R.CompactCover


