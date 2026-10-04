-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g54
-- name    : CK_CKLaneC2R_CompactCover_S05_g54
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T07:17:47.750089+00:00
-- url     : https://prove2.me/theorems/538b415e-2874-484b-9c11-b316493f08c5
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B032
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B033
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B034
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B035

namespace CKLaneC2R.CompactCover

theorem strip5_s097 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : a ≤ ((63837/64000 : ℚ) : ℝ)) (h551 : ¬ (a ≤ ((5103/5120 : ℚ) : ℝ))) (h582 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h588 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h591 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h594 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h597 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) (h600 : ¬ (z ≤ ((63023/64000 : ℚ) : ℝ))) (h603 : z ≤ ((126959/128000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h604 : z ≤ ((50601/51200 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B031.c621_pos (not_le.mp h551).le h550 (not_le.mp h600).le h604
  · -- right
    by_cases h605 : z ≤ ((506923/512000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B032.c642_pos (not_le.mp h551).le h550 (not_le.mp h604).le h605
    · -- right
      exact CKLaneC2R.Cells.S05.B032.c643_pos (not_le.mp h551).le h550 (not_le.mp h605).le h603

theorem strip5_s098 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : a ≤ ((63837/64000 : ℚ) : ℝ)) (h551 : ¬ (a ≤ ((5103/5120 : ℚ) : ℝ))) (h582 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h588 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h591 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h594 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h597 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) (h600 : ¬ (z ≤ ((63023/64000 : ℚ) : ℝ))) (h603 : ¬ (z ≤ ((126959/128000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h606 : z ≤ ((254831/256000 : ℚ) : ℝ)
  · -- left
    by_cases h607 : z ≤ ((508749/512000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B033.c663_pos (not_le.mp h551).le h550 (not_le.mp h603).le h607
    · -- right
      by_cases h608 : a ≤ ((255249/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B033.c676_pos (not_le.mp h551).le h608 (not_le.mp h607).le h606
      · -- right
        exact CKLaneC2R.Cells.S05.B033.c677_pos (not_le.mp h608).le h550 (not_le.mp h607).le h606
  · -- right
    by_cases h609 : z ≤ ((20423/20480 : ℚ) : ℝ)
    · -- left
      by_cases h610 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B034.c687_pos (not_le.mp h551).le h550 (not_le.mp h606).le h610
      · -- right
        by_cases h611 : a ≤ ((255249/256000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B034.c692_pos (not_le.mp h551).le h611 (not_le.mp h610).le h609
        · -- right
          exact CKLaneC2R.Cells.S05.B034.c693_pos (not_le.mp h611).le h550 (not_le.mp h610).le h609
    · -- right
      by_cases h612 : a ≤ ((255249/256000 : ℚ) : ℝ)
      · -- left
        by_cases h613 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B034.c698_pos (not_le.mp h551).le h612 (not_le.mp h609).le h613
        · -- right
          exact CKLaneC2R.Cells.S05.B035.c700_pos (not_le.mp h551).le h612 (not_le.mp h613).le hz2
      · -- right
        by_cases h614 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B034.c699_pos (not_le.mp h612).le h550 (not_le.mp h609).le h614
        · -- right
          by_cases h615 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B035.c708_pos (not_le.mp h612).le h550 (not_le.mp h614).le h615
          · -- right
            exact CKLaneC2R.Cells.S05.B035.c709_pos (not_le.mp h612).le h550 (not_le.mp h615).le hz2

end CKLaneC2R.CompactCover


