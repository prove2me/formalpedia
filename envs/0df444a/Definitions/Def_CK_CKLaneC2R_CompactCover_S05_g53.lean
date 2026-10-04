-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g53
-- name    : CK_CKLaneC2R_CompactCover_S05_g53
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T23:37:15.538691+00:00
-- url     : https://prove2.me/theorems/c09f8c42-8795-4092-9ad8-422e19ce7d19
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B025
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B026
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B028
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B029

namespace CKLaneC2R.CompactCover

theorem strip5_s095 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : a ≤ ((63837/64000 : ℚ) : ℝ)) (h551 : ¬ (a ≤ ((5103/5120 : ℚ) : ℝ))) (h582 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h588 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h591 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h594 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h597 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h598 : z ≤ ((61197/64000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B025.c510_pos (not_le.mp h551).le h550 (not_le.mp h594).le h598
  · -- right
    by_cases h599 : z ≤ ((123307/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B026.c538_pos (not_le.mp h551).le h550 (not_le.mp h598).le h599
    · -- right
      exact CKLaneC2R.Cells.S05.B026.c539_pos (not_le.mp h551).le h550 (not_le.mp h599).le h597

theorem strip5_s096 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : a ≤ ((63837/64000 : ℚ) : ℝ)) (h551 : ¬ (a ≤ ((5103/5120 : ℚ) : ℝ))) (h582 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h588 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h591 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h594 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h597 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) (h600 : z ≤ ((63023/64000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h601 : z ≤ ((125133/128000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B028.c573_pos (not_le.mp h551).le h550 (not_le.mp h597).le h601
  · -- right
    by_cases h602 : z ≤ ((251179/256000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B029.c597_pos (not_le.mp h551).le h550 (not_le.mp h601).le h602
    · -- right
      exact CKLaneC2R.Cells.S05.B029.c598_pos (not_le.mp h551).le h550 (not_le.mp h602).le h600

end CKLaneC2R.CompactCover


