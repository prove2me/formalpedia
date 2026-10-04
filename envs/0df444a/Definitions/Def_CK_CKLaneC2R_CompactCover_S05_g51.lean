-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g51
-- name    : CK_CKLaneC2R_CompactCover_S05_g51
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T23:18:10.536882+00:00
-- url     : https://prove2.me/theorems/c275f9fe-aa35-49ce-98e7-b17f1dc5e247
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B010
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B011
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B015

namespace CKLaneC2R.CompactCover

theorem strip5_s091 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : a ≤ ((63837/64000 : ℚ) : ℝ)) (h551 : ¬ (a ≤ ((5103/5120 : ℚ) : ℝ))) (h582 : z ≤ ((217/400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h583 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h584 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h585 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        by_cases h586 : a ≤ ((255249/256000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B018.c375_pos (not_le.mp h551).le h586 hz1 h585
        · -- right
          exact CKLaneC2R.Cells.S05.B018.c376_pos (not_le.mp h586).le h550 hz1 h585
      · -- right
        exact CKLaneC2R.Cells.S05.B014.c298_pos (not_le.mp h551).le h550 (not_le.mp h585).le h584
    · -- right
      exact CKLaneC2R.Cells.S05.B010.c214_pos (not_le.mp h551).le h550 (not_le.mp h584).le h583
  · -- right
    by_cases h587 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B010.c218_pos (not_le.mp h551).le h550 (not_le.mp h583).le h587
    · -- right
      exact CKLaneC2R.Cells.S05.B011.c220_pos (not_le.mp h551).le h550 (not_le.mp h587).le h582

theorem strip5_s092 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : a ≤ ((63837/64000 : ℚ) : ℝ)) (h551 : ¬ (a ≤ ((5103/5120 : ℚ) : ℝ))) (h582 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h588 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h589 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B011.c232_pos (not_le.mp h551).le h550 (not_le.mp h582).le h589
  · -- right
    by_cases h590 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B015.c311_pos (not_le.mp h551).le h550 (not_le.mp h589).le h590
    · -- right
      exact CKLaneC2R.Cells.S05.B015.c312_pos (not_le.mp h551).le h550 (not_le.mp h590).le h588

end CKLaneC2R.CompactCover


