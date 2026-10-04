-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g61
-- name    : CK_CKLaneC2R_CompactCover_S05_g61
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T20:36:06.933442+00:00
-- url     : https://prove2.me/theorems/f9df7b3d-c0ab-4bb4-8416-ba662e7e1d0f
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B023
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B019
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B015
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B024

namespace CKLaneC2R.CompactCover

theorem strip5_s117 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : ¬ (a ≤ ((127773/128000 : ℚ) : ℝ))) (h667 : ¬ (a ≤ ((51129/51200 : ℚ) : ℝ))) (h694 : z ≤ ((217/400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h695 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h696 : a ≤ ((511389/512000 : ℚ) : ℝ)
    · -- left
      by_cases h697 : z ≤ ((1601/8000 : ℚ) : ℝ)
      · -- left
        by_cases h698 : z ≤ ((2289/16000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B023.c461_pos (not_le.mp h667).le h696 hz1 h698
        · -- right
          exact CKLaneC2R.Cells.S05.B023.c463_pos (not_le.mp h667).le h696 (not_le.mp h698).le h697
      · -- right
        exact CKLaneC2R.Cells.S05.B019.c383_pos (not_le.mp h667).le h696 (not_le.mp h697).le h695
    · -- right
      by_cases h699 : z ≤ ((1601/8000 : ℚ) : ℝ)
      · -- left
        by_cases h700 : z ≤ ((2289/16000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B023.c462_pos (not_le.mp h696).le ha2 hz1 h700
        · -- right
          exact CKLaneC2R.Cells.S05.B023.c464_pos (not_le.mp h696).le ha2 (not_le.mp h700).le h699
      · -- right
        exact CKLaneC2R.Cells.S05.B019.c384_pos (not_le.mp h696).le ha2 (not_le.mp h699).le h695
  · -- right
    by_cases h701 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h702 : a ≤ ((511389/512000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B019.c385_pos (not_le.mp h667).le h702 (not_le.mp h695).le h701
      · -- right
        exact CKLaneC2R.Cells.S05.B019.c386_pos (not_le.mp h702).le ha2 (not_le.mp h695).le h701
    · -- right
      exact CKLaneC2R.Cells.S05.B015.c308_pos (not_le.mp h667).le ha2 (not_le.mp h701).le h694

theorem strip5_s118 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : ¬ (a ≤ ((127773/128000 : ℚ) : ℝ))) (h667 : ¬ (a ≤ ((51129/51200 : ℚ) : ℝ))) (h694 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h703 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h704 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B015.c316_pos (not_le.mp h667).le ha2 (not_le.mp h694).le h704
  · -- right
    by_cases h705 : a ≤ ((511389/512000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B019.c387_pos (not_le.mp h667).le h705 (not_le.mp h704).le h703
    · -- right
      exact CKLaneC2R.Cells.S05.B019.c388_pos (not_le.mp h705).le ha2 (not_le.mp h704).le h703

theorem strip5_s119 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : ¬ (a ≤ ((127773/128000 : ℚ) : ℝ))) (h667 : ¬ (a ≤ ((51129/51200 : ℚ) : ℝ))) (h694 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h703 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h706 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h707 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B019.c396_pos (not_le.mp h667).le ha2 (not_le.mp h703).le h707
  · -- right
    exact CKLaneC2R.Cells.S05.B020.c400_pos (not_le.mp h667).le ha2 (not_le.mp h707).le h706

theorem strip5_s120 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : ¬ (a ≤ ((127773/128000 : ℚ) : ℝ))) (h667 : ¬ (a ≤ ((51129/51200 : ℚ) : ℝ))) (h694 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h703 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h706 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h708 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h709 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B024.c484_pos (not_le.mp h667).le ha2 (not_le.mp h706).le h709
  · -- right
    exact CKLaneC2R.Cells.S05.B024.c488_pos (not_le.mp h667).le ha2 (not_le.mp h709).le h708

end CKLaneC2R.CompactCover


