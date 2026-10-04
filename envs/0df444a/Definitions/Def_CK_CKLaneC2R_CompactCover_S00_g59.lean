-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g59
-- name    : CK_CKLaneC2R_CompactCover_S00_g59
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T18:59:53.432131+00:00
-- url     : https://prove2.me/theorems/217c7081-8dfe-45ae-9b9f-db7a63ca3274
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S00 (proof part of strip0)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S00 (proof part of strip0) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S00 (proof part of strip0).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B050
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B051

namespace CKLaneC2R.CompactCover

theorem strip0_s071 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : ¬ (a ≤ ((27/160 : ℚ) : ℝ))) (h693 : a ≤ ((11/64 : ℚ) : ℝ)) (h694 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h747 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h763 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h771 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h777 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h778 : z ≤ ((61197/64000 : ℚ) : ℝ)
  · -- left
    by_cases h779 : z ≤ ((121481/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B050.c1010_pos (not_le.mp h481).le h693 (not_le.mp h771).le h779
    · -- right
      exact CKLaneC2R.Cells.S00.B050.c1012_pos (not_le.mp h481).le h693 (not_le.mp h779).le h778
  · -- right
    by_cases h780 : z ≤ ((123307/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B050.c1018_pos (not_le.mp h481).le h693 (not_le.mp h778).le h780
    · -- right
      exact CKLaneC2R.Cells.S00.B051.c1020_pos (not_le.mp h481).le h693 (not_le.mp h780).le h777

end CKLaneC2R.CompactCover


