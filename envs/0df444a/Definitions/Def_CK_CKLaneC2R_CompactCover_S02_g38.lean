-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g38
-- name    : CK_CKLaneC2R_CompactCover_S02_g38
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T17:39:47.536048+00:00
-- url     : https://prove2.me/theorems/36c4a573-4509-4609-843b-f8d98c9628ac
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B005
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B009
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B010

namespace CKLaneC2R.CompactCover

theorem strip2_s057 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : a ≤ ((9/20 : ℚ) : ℝ)) (h535 : a ≤ ((17/40 : ℚ) : ℝ)) (h536 : ¬ (a ≤ ((33/80 : ℚ) : ℝ))) (h584 : z ≤ ((217/400 : ℚ) : ℝ)) (h585 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h600 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h601 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h602 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B005.c102_pos (not_le.mp h536).le h535 (not_le.mp h585).le h602
      · -- right
        exact CKLaneC2R.Cells.S02.B005.c103_pos (not_le.mp h536).le h535 (not_le.mp h602).le h601
    · -- right
      by_cases h603 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B005.c106_pos (not_le.mp h536).le h535 (not_le.mp h601).le h603
      · -- right
        exact CKLaneC2R.Cells.S02.B005.c107_pos (not_le.mp h536).le h535 (not_le.mp h603).le h600
  · -- right
    by_cases h604 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h605 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B005.c118_pos (not_le.mp h536).le h535 (not_le.mp h600).le h605
      · -- right
        exact CKLaneC2R.Cells.S02.B005.c119_pos (not_le.mp h536).le h535 (not_le.mp h605).le h604
    · -- right
      by_cases h606 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B006.c122_pos (not_le.mp h536).le h535 (not_le.mp h604).le h606
      · -- right
        exact CKLaneC2R.Cells.S02.B006.c123_pos (not_le.mp h536).le h535 (not_le.mp h606).le h584

theorem strip2_s058 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : a ≤ ((9/20 : ℚ) : ℝ)) (h535 : a ≤ ((17/40 : ℚ) : ℝ)) (h536 : ¬ (a ≤ ((33/80 : ℚ) : ℝ))) (h584 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h607 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h608 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h609 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h610 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B009.c196_pos (not_le.mp h536).le h535 (not_le.mp h584).le h610
      · -- right
        exact CKLaneC2R.Cells.S02.B009.c197_pos (not_le.mp h536).le h535 (not_le.mp h610).le h609
    · -- right
      by_cases h611 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B010.c200_pos (not_le.mp h536).le h535 (not_le.mp h609).le h611
      · -- right
        exact CKLaneC2R.Cells.S02.B010.c201_pos (not_le.mp h536).le h535 (not_le.mp h611).le h608
  · -- right
    by_cases h612 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h613 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B010.c210_pos (not_le.mp h536).le h535 (not_le.mp h608).le h613
      · -- right
        exact CKLaneC2R.Cells.S02.B010.c211_pos (not_le.mp h536).le h535 (not_le.mp h613).le h612
    · -- right
      by_cases h614 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B010.c214_pos (not_le.mp h536).le h535 (not_le.mp h612).le h614
      · -- right
        exact CKLaneC2R.Cells.S02.B010.c215_pos (not_le.mp h536).le h535 (not_le.mp h614).le h607

end CKLaneC2R.CompactCover


