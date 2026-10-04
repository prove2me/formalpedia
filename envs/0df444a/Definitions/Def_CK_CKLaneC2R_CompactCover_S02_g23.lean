-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g23
-- name    : CK_CKLaneC2R_CompactCover_S02_g23
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T05:15:18.948996+00:00
-- url     : https://prove2.me/theorems/efd468cf-be39-4116-9ada-df5d101c333f
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S02 (proof part of strip2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S02 (proof part of strip2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S02 (proof part of strip2).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B001
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B002
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B009

namespace CKLaneC2R.CompactCover

theorem strip2_s036 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : a ≤ ((3/8 : ℚ) : ℝ)) (h316 : ¬ (a ≤ ((29/80 : ℚ) : ℝ))) (h375 : z ≤ ((217/400 : ℚ) : ℝ)) (h376 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h398 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h399 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h400 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B001.c35_pos (not_le.mp h316).le h315 (not_le.mp h376).le h400
      · -- right
        exact CKLaneC2R.Cells.S02.B001.c36_pos (not_le.mp h316).le h315 (not_le.mp h400).le h399
    · -- right
      by_cases h401 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B001.c39_pos (not_le.mp h316).le h315 (not_le.mp h399).le h401
      · -- right
        exact CKLaneC2R.Cells.S02.B002.c40_pos (not_le.mp h316).le h315 (not_le.mp h401).le h398
  · -- right
    by_cases h402 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h403 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B002.c51_pos (not_le.mp h316).le h315 (not_le.mp h398).le h403
      · -- right
        exact CKLaneC2R.Cells.S02.B002.c52_pos (not_le.mp h316).le h315 (not_le.mp h403).le h402
    · -- right
      by_cases h404 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B002.c55_pos (not_le.mp h316).le h315 (not_le.mp h402).le h404
      · -- right
        exact CKLaneC2R.Cells.S02.B002.c56_pos (not_le.mp h316).le h315 (not_le.mp h404).le h375

theorem strip2_s037 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((7/20 : ℚ) : ℝ))) (h315 : a ≤ ((3/8 : ℚ) : ℝ)) (h316 : ¬ (a ≤ ((29/80 : ℚ) : ℝ))) (h375 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h405 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h406 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h407 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h408 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B008.c164_pos (not_le.mp h316).le h315 (not_le.mp h375).le h408
      · -- right
        exact CKLaneC2R.Cells.S02.B008.c165_pos (not_le.mp h316).le h315 (not_le.mp h408).le h407
    · -- right
      by_cases h409 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B008.c168_pos (not_le.mp h316).le h315 (not_le.mp h407).le h409
      · -- right
        exact CKLaneC2R.Cells.S02.B008.c169_pos (not_le.mp h316).le h315 (not_le.mp h409).le h406
  · -- right
    by_cases h410 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h411 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B009.c180_pos (not_le.mp h316).le h315 (not_le.mp h406).le h411
      · -- right
        exact CKLaneC2R.Cells.S02.B009.c181_pos (not_le.mp h316).le h315 (not_le.mp h411).le h410
    · -- right
      by_cases h412 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B009.c184_pos (not_le.mp h316).le h315 (not_le.mp h410).le h412
      · -- right
        exact CKLaneC2R.Cells.S02.B009.c185_pos (not_le.mp h316).le h315 (not_le.mp h412).le h405

end CKLaneC2R.CompactCover


