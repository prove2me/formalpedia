-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g43
-- name    : CK_CKLaneC2R_CompactCover_S05_g43
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T19:36:23.858916+00:00
-- url     : https://prove2.me/theorems/ce335148-2de0-4e57-94d9-d2bf671fa374
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B010
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B007
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B011

namespace CKLaneC2R.CompactCover

theorem strip5_s077 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : a ≤ ((31869/32000 : ℚ) : ℝ)) (h474 : ¬ (a ≤ ((63639/64000 : ℚ) : ℝ))) (h507 : z ≤ ((217/400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h508 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h509 : a ≤ ((127377/128000 : ℚ) : ℝ)
    · -- left
      by_cases h510 : z ≤ ((1601/8000 : ℚ) : ℝ)
      · -- left
        by_cases h511 : z ≤ ((2289/16000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B014.c292_pos (not_le.mp h474).le h509 hz1 h511
        · -- right
          exact CKLaneC2R.Cells.S05.B014.c294_pos (not_le.mp h474).le h509 (not_le.mp h511).le h510
      · -- right
        exact CKLaneC2R.Cells.S05.B010.c211_pos (not_le.mp h474).le h509 (not_le.mp h510).le h508
    · -- right
      by_cases h512 : z ≤ ((1601/8000 : ℚ) : ℝ)
      · -- left
        by_cases h513 : z ≤ ((2289/16000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B014.c293_pos (not_le.mp h509).le h473 hz1 h513
        · -- right
          exact CKLaneC2R.Cells.S05.B014.c295_pos (not_le.mp h509).le h473 (not_le.mp h513).le h512
      · -- right
        exact CKLaneC2R.Cells.S05.B010.c212_pos (not_le.mp h509).le h473 (not_le.mp h512).le h508
  · -- right
    by_cases h514 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h515 : a ≤ ((127377/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B010.c215_pos (not_le.mp h474).le h515 (not_le.mp h508).le h514
      · -- right
        exact CKLaneC2R.Cells.S05.B010.c216_pos (not_le.mp h515).le h473 (not_le.mp h508).le h514
    · -- right
      exact CKLaneC2R.Cells.S05.B007.c148_pos (not_le.mp h474).le h473 (not_le.mp h514).le h507

theorem strip5_s078 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : a ≤ ((31869/32000 : ℚ) : ℝ)) (h474 : ¬ (a ≤ ((63639/64000 : ℚ) : ℝ))) (h507 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h516 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h517 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h518 : a ≤ ((127377/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B011.c225_pos (not_le.mp h474).le h518 (not_le.mp h507).le h517
    · -- right
      exact CKLaneC2R.Cells.S05.B011.c226_pos (not_le.mp h518).le h473 (not_le.mp h507).le h517
  · -- right
    by_cases h519 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B011.c229_pos (not_le.mp h474).le h473 (not_le.mp h517).le h519
    · -- right
      exact CKLaneC2R.Cells.S05.B011.c230_pos (not_le.mp h474).le h473 (not_le.mp h519).le h516

end CKLaneC2R.CompactCover


