-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g59
-- name    : CK_CKLaneC2R_CompactCover_S05_g59
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T01:39:29.547458+00:00
-- url     : https://prove2.me/theorems/21ce8da9-22c3-48ef-8599-77383d723928
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B019
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B015
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B024
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B030

namespace CKLaneC2R.CompactCover

theorem strip5_s110 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : ¬ (a ≤ ((127773/128000 : ℚ) : ℝ))) (h667 : a ≤ ((51129/51200 : ℚ) : ℝ)) (h668 : z ≤ ((217/400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h669 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h670 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h671 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B019.c381_pos (not_le.mp h616).le h667 hz1 h671
      · -- right
        exact CKLaneC2R.Cells.S05.B019.c382_pos (not_le.mp h616).le h667 (not_le.mp h671).le h670
    · -- right
      exact CKLaneC2R.Cells.S05.B015.c301_pos (not_le.mp h616).le h667 (not_le.mp h670).le h669
  · -- right
    by_cases h672 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B015.c306_pos (not_le.mp h616).le h667 (not_le.mp h669).le h672
    · -- right
      exact CKLaneC2R.Cells.S05.B015.c307_pos (not_le.mp h616).le h667 (not_le.mp h672).le h668

theorem strip5_s111 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : ¬ (a ≤ ((127773/128000 : ℚ) : ℝ))) (h667 : a ≤ ((51129/51200 : ℚ) : ℝ)) (h668 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h673 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h674 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B015.c315_pos (not_le.mp h616).le h667 (not_le.mp h668).le h674
  · -- right
    exact CKLaneC2R.Cells.S05.B015.c319_pos (not_le.mp h616).le h667 (not_le.mp h674).le h673

theorem strip5_s112 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : ¬ (a ≤ ((127773/128000 : ℚ) : ℝ))) (h667 : a ≤ ((51129/51200 : ℚ) : ℝ)) (h668 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h673 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h675 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h676 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B019.c395_pos (not_le.mp h616).le h667 (not_le.mp h673).le h676
  · -- right
    exact CKLaneC2R.Cells.S05.B019.c399_pos (not_le.mp h616).le h667 (not_le.mp h676).le h675

theorem strip5_s113 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : ¬ (a ≤ ((127773/128000 : ℚ) : ℝ))) (h667 : a ≤ ((51129/51200 : ℚ) : ℝ)) (h668 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h673 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h675 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h677 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h678 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B024.c483_pos (not_le.mp h616).le h667 (not_le.mp h675).le h678
  · -- right
    exact CKLaneC2R.Cells.S05.B024.c487_pos (not_le.mp h616).le h667 (not_le.mp h678).le h677

theorem strip5_s114 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : ¬ (a ≤ ((127773/128000 : ℚ) : ℝ))) (h667 : a ≤ ((51129/51200 : ℚ) : ℝ)) (h668 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h673 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h675 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h677 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h679 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h680 : z ≤ ((61197/64000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B027.c542_pos (not_le.mp h616).le h667 (not_le.mp h677).le h680
  · -- right
    exact CKLaneC2R.Cells.S05.B027.c546_pos (not_le.mp h616).le h667 (not_le.mp h680).le h679

theorem strip5_s115 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : ¬ (a ≤ ((127773/128000 : ℚ) : ℝ))) (h667 : a ≤ ((51129/51200 : ℚ) : ℝ)) (h668 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h673 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h675 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h677 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h679 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) (h681 : z ≤ ((63023/64000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h682 : z ≤ ((125133/128000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B030.c601_pos (not_le.mp h616).le h667 (not_le.mp h679).le h682
  · -- right
    exact CKLaneC2R.Cells.S05.B030.c603_pos (not_le.mp h616).le h667 (not_le.mp h682).le h681

end CKLaneC2R.CompactCover


