-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g30
-- name    : CK_CKLaneC2R_CompactCover_S00_g30
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T15:14:38.015651+00:00
-- url     : https://prove2.me/theorems/1419e681-7733-481d-a191-107b88de14bc
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S00 (proof part of strip0) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S00 (proof part of strip0).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B069
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B053
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B054
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B055
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B057
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B034

namespace CKLaneC2R.CompactCover

theorem strip0_s036 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((5/32 : ℚ) : ℝ))) (h253 : ¬ (a ≤ ((51/320 : ℚ) : ℝ))) (h369 : z ≤ ((217/400 : ℚ) : ℝ)) (h370 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h371 : a ≤ ((103/640 : ℚ) : ℝ)) (h372 : z ≤ ((1601/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h373 : z ≤ ((2289/16000 : ℚ) : ℝ)
  · -- left
    by_cases h374 : z ≤ ((733/6400 : ℚ) : ℝ)
    · -- left
      by_cases h375 : z ≤ ((6417/64000 : ℚ) : ℝ)
      · -- left
        by_cases h376 : z ≤ ((11921/128000 : ℚ) : ℝ)
        · -- left
          by_cases h377 : z ≤ ((22929/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B069.c1398_pos (not_le.mp h253).le h371 hz1 h377
          · -- right
            exact CKLaneC2R.Cells.S00.B069.c1399_pos (not_le.mp h253).le h371 (not_le.mp h377).le h376
        · -- right
          exact CKLaneC2R.Cells.S00.B053.c1066_pos (not_le.mp h253).le h371 (not_le.mp h376).le h375
      · -- right
        by_cases h378 : z ≤ ((13747/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B053.c1072_pos (not_le.mp h253).le h371 (not_le.mp h375).le h378
        · -- right
          exact CKLaneC2R.Cells.S00.B053.c1074_pos (not_le.mp h253).le h371 (not_le.mp h378).le h374
    · -- right
      by_cases h379 : z ≤ ((8243/64000 : ℚ) : ℝ)
      · -- left
        by_cases h380 : z ≤ ((15573/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B054.c1096_pos (not_le.mp h253).le h371 (not_le.mp h374).le h380
        · -- right
          exact CKLaneC2R.Cells.S00.B054.c1098_pos (not_le.mp h253).le h371 (not_le.mp h380).le h379
      · -- right
        by_cases h381 : z ≤ ((17399/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B055.c1104_pos (not_le.mp h253).le h371 (not_le.mp h379).le h381
        · -- right
          exact CKLaneC2R.Cells.S00.B055.c1106_pos (not_le.mp h253).le h371 (not_le.mp h381).le h373
  · -- right
    by_cases h382 : z ≤ ((5491/32000 : ℚ) : ℝ)
    · -- left
      by_cases h383 : z ≤ ((10069/64000 : ℚ) : ℝ)
      · -- left
        by_cases h384 : z ≤ ((769/5120 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B057.c1140_pos (not_le.mp h253).le h371 (not_le.mp h373).le h384
        · -- right
          exact CKLaneC2R.Cells.S00.B057.c1142_pos (not_le.mp h253).le h371 (not_le.mp h384).le h383
      · -- right
        by_cases h385 : z ≤ ((21051/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B057.c1144_pos (not_le.mp h253).le h371 (not_le.mp h383).le h385
        · -- right
          exact CKLaneC2R.Cells.S00.B057.c1145_pos (not_le.mp h253).le h371 (not_le.mp h385).le h382
    · -- right
      by_cases h386 : z ≤ ((2379/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B034.c680_pos (not_le.mp h253).le h371 (not_le.mp h382).le h386
      · -- right
        exact CKLaneC2R.Cells.S00.B034.c682_pos (not_le.mp h253).le h371 (not_le.mp h386).le h372

end CKLaneC2R.CompactCover


