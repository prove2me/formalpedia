-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g57
-- name    : CK_CKLaneC2R_CompactCover_S05_g57
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T19:51:17.537799+00:00
-- url     : https://prove2.me/theorems/3f5ea7a6-6e7a-4ff7-a964-595e3d2364a1
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
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B019
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B015
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B024
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B027

namespace CKLaneC2R.CompactCover

theorem strip5_s104 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : a ≤ ((127773/128000 : ℚ) : ℝ)) (h617 : ¬ (a ≤ ((255447/256000 : ℚ) : ℝ))) (h642 : z ≤ ((217/400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h643 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h644 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h645 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B018.c378_pos (not_le.mp h617).le h616 hz1 h645
      · -- right
        exact CKLaneC2R.Cells.S05.B019.c380_pos (not_le.mp h617).le h616 (not_le.mp h645).le h644
    · -- right
      exact CKLaneC2R.Cells.S05.B015.c300_pos (not_le.mp h617).le h616 (not_le.mp h644).le h643
  · -- right
    by_cases h646 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B015.c303_pos (not_le.mp h617).le h616 (not_le.mp h643).le h646
    · -- right
      exact CKLaneC2R.Cells.S05.B015.c305_pos (not_le.mp h617).le h616 (not_le.mp h646).le h642

theorem strip5_s105 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : a ≤ ((127773/128000 : ℚ) : ℝ)) (h617 : ¬ (a ≤ ((255447/256000 : ℚ) : ℝ))) (h642 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h647 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h648 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B015.c314_pos (not_le.mp h617).le h616 (not_le.mp h642).le h648
  · -- right
    exact CKLaneC2R.Cells.S05.B015.c318_pos (not_le.mp h617).le h616 (not_le.mp h648).le h647

theorem strip5_s106 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : a ≤ ((127773/128000 : ℚ) : ℝ)) (h617 : ¬ (a ≤ ((255447/256000 : ℚ) : ℝ))) (h642 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h647 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h649 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h650 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B019.c394_pos (not_le.mp h617).le h616 (not_le.mp h647).le h650
  · -- right
    exact CKLaneC2R.Cells.S05.B019.c398_pos (not_le.mp h617).le h616 (not_le.mp h650).le h649

theorem strip5_s107 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : a ≤ ((127773/128000 : ℚ) : ℝ)) (h617 : ¬ (a ≤ ((255447/256000 : ℚ) : ℝ))) (h642 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h647 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h649 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h651 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h652 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B024.c482_pos (not_le.mp h617).le h616 (not_le.mp h649).le h652
  · -- right
    exact CKLaneC2R.Cells.S05.B024.c486_pos (not_le.mp h617).le h616 (not_le.mp h652).le h651

theorem strip5_s108 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : a ≤ ((127773/128000 : ℚ) : ℝ)) (h617 : ¬ (a ≤ ((255447/256000 : ℚ) : ℝ))) (h642 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h647 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h649 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h651 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h653 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h654 : z ≤ ((61197/64000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B027.c541_pos (not_le.mp h617).le h616 (not_le.mp h651).le h654
  · -- right
    exact CKLaneC2R.Cells.S05.B027.c545_pos (not_le.mp h617).le h616 (not_le.mp h654).le h653

end CKLaneC2R.CompactCover


