-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g55
-- name    : CK_CKLaneC2R_CompactCover_S05_g55
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T05:33:15.952795+00:00
-- url     : https://prove2.me/theorems/63d5713f-ddb6-47fa-ae8d-c0bdb8e2d43a
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
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B015
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B019
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B024

namespace CKLaneC2R.CompactCover

theorem strip5_s099 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : a ≤ ((127773/128000 : ℚ) : ℝ)) (h617 : a ≤ ((255447/256000 : ℚ) : ℝ)) (h618 : z ≤ ((217/400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h619 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h620 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h621 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B018.c377_pos (not_le.mp h550).le h617 hz1 h621
      · -- right
        exact CKLaneC2R.Cells.S05.B018.c379_pos (not_le.mp h550).le h617 (not_le.mp h621).le h620
    · -- right
      exact CKLaneC2R.Cells.S05.B014.c299_pos (not_le.mp h550).le h617 (not_le.mp h620).le h619
  · -- right
    by_cases h622 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B015.c302_pos (not_le.mp h550).le h617 (not_le.mp h619).le h622
    · -- right
      exact CKLaneC2R.Cells.S05.B015.c304_pos (not_le.mp h550).le h617 (not_le.mp h622).le h618

theorem strip5_s100 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : a ≤ ((127773/128000 : ℚ) : ℝ)) (h617 : a ≤ ((255447/256000 : ℚ) : ℝ)) (h618 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h623 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h624 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B015.c313_pos (not_le.mp h550).le h617 (not_le.mp h618).le h624
  · -- right
    exact CKLaneC2R.Cells.S05.B015.c317_pos (not_le.mp h550).le h617 (not_le.mp h624).le h623

theorem strip5_s101 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : a ≤ ((127773/128000 : ℚ) : ℝ)) (h617 : a ≤ ((255447/256000 : ℚ) : ℝ)) (h618 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h623 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h625 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h626 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B019.c393_pos (not_le.mp h550).le h617 (not_le.mp h623).le h626
  · -- right
    exact CKLaneC2R.Cells.S05.B019.c397_pos (not_le.mp h550).le h617 (not_le.mp h626).le h625

theorem strip5_s102 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : a ≤ ((127773/128000 : ℚ) : ℝ)) (h617 : a ≤ ((255447/256000 : ℚ) : ℝ)) (h618 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h623 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h625 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h627 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h628 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B024.c481_pos (not_le.mp h550).le h617 (not_le.mp h625).le h628
  · -- right
    exact CKLaneC2R.Cells.S05.B024.c485_pos (not_le.mp h550).le h617 (not_le.mp h628).le h627

end CKLaneC2R.CompactCover


