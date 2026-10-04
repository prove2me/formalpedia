-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g73
-- name    : CK_CKLaneC2R_CompactCover_S00_g73
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T13:58:55.064369+00:00
-- url     : https://prove2.me/theorems/40eb8d3e-6a07-42cf-abea-c413a06d0763
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B051

namespace CKLaneC2R.CompactCover

theorem strip0_s089 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : a ≤ ((29/160 : ℚ) : ℝ)) (h893 : a ≤ ((57/320 : ℚ) : ℝ)) (h894 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h943 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h959 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h967 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h973 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h974 : z ≤ ((61197/64000 : ℚ) : ℝ)
  · -- left
    by_cases h975 : z ≤ ((121481/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B051.c1022_pos (not_le.mp h0).le h893 (not_le.mp h967).le h975
    · -- right
      exact CKLaneC2R.Cells.S00.B051.c1024_pos (not_le.mp h0).le h893 (not_le.mp h975).le h974
  · -- right
    by_cases h976 : z ≤ ((123307/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S00.B051.c1030_pos (not_le.mp h0).le h893 (not_le.mp h974).le h976
    · -- right
      exact CKLaneC2R.Cells.S00.B051.c1032_pos (not_le.mp h0).le h893 (not_le.mp h976).le h973

end CKLaneC2R.CompactCover


