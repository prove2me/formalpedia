-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g44
-- name    : CK_CKLaneC2R_CompactCover_S05_g44
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T13:38:43.38398+00:00
-- url     : https://prove2.me/theorems/a6ea3b7e-9e4d-428f-aae3-2a656eb0a2e5
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B012
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B025

namespace CKLaneC2R.CompactCover

theorem strip5_s079 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : a ≤ ((31869/32000 : ℚ) : ℝ)) (h474 : ¬ (a ≤ ((63639/64000 : ℚ) : ℝ))) (h507 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h516 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h520 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h521 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B012.c246_pos (not_le.mp h474).le h473 (not_le.mp h516).le h521
  · -- right
    by_cases h522 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B016.c326_pos (not_le.mp h474).le h473 (not_le.mp h521).le h522
    · -- right
      exact CKLaneC2R.Cells.S05.B016.c327_pos (not_le.mp h474).le h473 (not_le.mp h522).le h520

theorem strip5_s080 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : a ≤ ((31869/32000 : ℚ) : ℝ)) (h474 : ¬ (a ≤ ((63639/64000 : ℚ) : ℝ))) (h507 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h516 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h520 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h523 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h524 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B017.c356_pos (not_le.mp h474).le h473 (not_le.mp h520).le h524
  · -- right
    by_cases h525 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B020.c415_pos (not_le.mp h474).le h473 (not_le.mp h524).le h525
    · -- right
      exact CKLaneC2R.Cells.S05.B020.c416_pos (not_le.mp h474).le h473 (not_le.mp h525).le h523

theorem strip5_s081 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : a ≤ ((31869/32000 : ℚ) : ℝ)) (h474 : ¬ (a ≤ ((63639/64000 : ℚ) : ℝ))) (h507 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h516 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h520 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h523 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h526 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h527 : z ≤ ((61197/64000 : ℚ) : ℝ)
  · -- left
    by_cases h528 : a ≤ ((127377/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B025.c503_pos (not_le.mp h474).le h528 (not_le.mp h523).le h527
    · -- right
      exact CKLaneC2R.Cells.S05.B025.c504_pos (not_le.mp h528).le h473 (not_le.mp h523).le h527
  · -- right
    by_cases h529 : z ≤ ((123307/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B025.c507_pos (not_le.mp h474).le h473 (not_le.mp h527).le h529
    · -- right
      exact CKLaneC2R.Cells.S05.B025.c508_pos (not_le.mp h474).le h473 (not_le.mp h529).le h526

end CKLaneC2R.CompactCover


