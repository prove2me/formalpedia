-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g17
-- name    : CK_CKLaneC2R_CompactCover_S03_g17
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T02:55:00.190403+00:00
-- url     : https://prove2.me/theorems/781cdd85-176a-4ccb-b9b9-d8655d66d31e
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S03 (proof part of strip3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S03 (proof part of strip3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S03 (proof part of strip3).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S03_B005
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B006

namespace CKLaneC2R.CompactCover

theorem strip3_s025 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((3/5 : ℚ) : ℝ))) (h220 : a ≤ ((13/20 : ℚ) : ℝ)) (h221 : ¬ (a ≤ ((5/8 : ℚ) : ℝ))) (h268 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h290 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h291 : a ≤ ((51/80 : ℚ) : ℝ)
  · -- left
    by_cases h292 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h293 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B005.c119_pos (not_le.mp h221).le h291 (not_le.mp h268).le h293
      · -- right
        exact CKLaneC2R.Cells.S03.B006.c121_pos (not_le.mp h221).le h291 (not_le.mp h293).le h292
    · -- right
      by_cases h294 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B006.c127_pos (not_le.mp h221).le h291 (not_le.mp h292).le h294
      · -- right
        exact CKLaneC2R.Cells.S03.B006.c129_pos (not_le.mp h221).le h291 (not_le.mp h294).le h290
  · -- right
    by_cases h295 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h296 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B006.c120_pos (not_le.mp h291).le h220 (not_le.mp h268).le h296
      · -- right
        exact CKLaneC2R.Cells.S03.B006.c122_pos (not_le.mp h291).le h220 (not_le.mp h296).le h295
    · -- right
      by_cases h297 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B006.c128_pos (not_le.mp h291).le h220 (not_le.mp h295).le h297
      · -- right
        exact CKLaneC2R.Cells.S03.B006.c130_pos (not_le.mp h291).le h220 (not_le.mp h297).le h290

end CKLaneC2R.CompactCover


