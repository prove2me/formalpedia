-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g56
-- name    : CK_CKLaneC2R_CompactCover_S00_g56
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T19:18:26.926986+00:00
-- url     : https://prove2.me/theorems/ab020a96-ed6b-4a6e-a00f-78ca8f5e79fa
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B007
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B009

namespace CKLaneC2R.CompactCover

theorem strip0_s067 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : ¬ (a ≤ ((27/160 : ℚ) : ℝ))) (h693 : a ≤ ((11/64 : ℚ) : ℝ)) (h694 : z ≤ ((217/400 : ℚ) : ℝ)) (h695 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h732 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h733 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h734 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h735 : z ≤ ((841/2560 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B007.c143_pos (not_le.mp h481).le h693 (not_le.mp h695).le h735
        · -- right
          exact CKLaneC2R.Cells.S00.B007.c144_pos (not_le.mp h481).le h693 (not_le.mp h735).le h734
      · -- right
        by_cases h736 : z ≤ ((22851/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B007.c147_pos (not_le.mp h481).le h693 (not_le.mp h734).le h736
        · -- right
          exact CKLaneC2R.Cells.S00.B007.c148_pos (not_le.mp h481).le h693 (not_le.mp h736).le h733
    · -- right
      by_cases h737 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        by_cases h738 : z ≤ ((24677/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B007.c159_pos (not_le.mp h481).le h693 (not_le.mp h733).le h738
        · -- right
          exact CKLaneC2R.Cells.S00.B008.c160_pos (not_le.mp h481).le h693 (not_le.mp h738).le h737
      · -- right
        by_cases h739 : z ≤ ((26503/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B008.c163_pos (not_le.mp h481).le h693 (not_le.mp h737).le h739
        · -- right
          exact CKLaneC2R.Cells.S00.B008.c164_pos (not_le.mp h481).le h693 (not_le.mp h739).le h732
  · -- right
    by_cases h740 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h741 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        by_cases h742 : z ≤ ((28329/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B008.c175_pos (not_le.mp h481).le h693 (not_le.mp h732).le h742
        · -- right
          exact CKLaneC2R.Cells.S00.B008.c176_pos (not_le.mp h481).le h693 (not_le.mp h742).le h741
      · -- right
        by_cases h743 : z ≤ ((6031/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B008.c179_pos (not_le.mp h481).le h693 (not_le.mp h741).le h743
        · -- right
          exact CKLaneC2R.Cells.S00.B009.c180_pos (not_le.mp h481).le h693 (not_le.mp h743).le h740
    · -- right
      by_cases h744 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        by_cases h745 : z ≤ ((31981/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B009.c191_pos (not_le.mp h481).le h693 (not_le.mp h740).le h745
        · -- right
          exact CKLaneC2R.Cells.S00.B009.c192_pos (not_le.mp h481).le h693 (not_le.mp h745).le h744
      · -- right
        by_cases h746 : z ≤ ((33807/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B009.c195_pos (not_le.mp h481).le h693 (not_le.mp h744).le h746
        · -- right
          exact CKLaneC2R.Cells.S00.B009.c196_pos (not_le.mp h481).le h693 (not_le.mp h746).le h694

end CKLaneC2R.CompactCover


