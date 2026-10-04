-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g08
-- name    : CK_CKLaneC2R_CompactCover_S01_g08
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T19:06:25.878157+00:00
-- url     : https://prove2.me/theorems/c43fb5cb-a658-47c5-8e7e-479a7dc5c0f9
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S01 (proof part of strip1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S01 (proof part of strip1).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B044
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B053

namespace CKLaneC2R.CompactCover

theorem strip1_s009 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : a ≤ ((33/160 : ℚ) : ℝ)) (h4 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h66 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h82 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h92 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h100 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h101 : z ≤ ((61197/64000 : ℚ) : ℝ)
  · -- left
    by_cases h102 : z ≤ ((121481/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B044.c882_pos ha1 h3 (not_le.mp h92).le h102
    · -- right
      exact CKLaneC2R.Cells.S01.B044.c883_pos ha1 h3 (not_le.mp h102).le h101
  · -- right
    by_cases h103 : z ≤ ((123307/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B044.c886_pos ha1 h3 (not_le.mp h101).le h103
    · -- right
      by_cases h104 : a ≤ ((13/64 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B053.c1072_pos ha1 h104 (not_le.mp h103).le h100
      · -- right
        exact CKLaneC2R.Cells.S01.B053.c1073_pos (not_le.mp h104).le h3 (not_le.mp h103).le h100

end CKLaneC2R.CompactCover


