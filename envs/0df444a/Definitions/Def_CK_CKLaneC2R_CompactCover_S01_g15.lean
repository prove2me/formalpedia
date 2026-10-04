-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g15
-- name    : CK_CKLaneC2R_CompactCover_S01_g15
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T14:38:36.657336+00:00
-- url     : https://prove2.me/theorems/fd99991d-3a3b-4332-b924-7065d5846e4f
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

namespace CKLaneC2R.CompactCover

theorem strip1_s020 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : ¬ (a ≤ ((33/160 : ℚ) : ℝ))) (h118 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h175 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h191 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h199 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h207 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h208 : z ≤ ((61197/64000 : ℚ) : ℝ)
  · -- left
    by_cases h209 : z ≤ ((121481/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B044.c884_pos (not_le.mp h3).le h2 (not_le.mp h199).le h209
    · -- right
      exact CKLaneC2R.Cells.S01.B044.c885_pos (not_le.mp h3).le h2 (not_le.mp h209).le h208
  · -- right
    by_cases h210 : z ≤ ((123307/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B044.c887_pos (not_le.mp h3).le h2 (not_le.mp h208).le h210
    · -- right
      exact CKLaneC2R.Cells.S01.B044.c888_pos (not_le.mp h3).le h2 (not_le.mp h210).le h207

end CKLaneC2R.CompactCover


