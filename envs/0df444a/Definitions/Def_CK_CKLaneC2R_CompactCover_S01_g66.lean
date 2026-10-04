-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g66
-- name    : CK_CKLaneC2R_CompactCover_S01_g66
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T06:54:06.639337+00:00
-- url     : https://prove2.me/theorems/4ba9fdc3-190d-4895-8abd-471a25396e23
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B004
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B005
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B028

namespace CKLaneC2R.CompactCover

theorem strip1_s094 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : ¬ (a ≤ ((21/80 : ℚ) : ℝ))) (h880 : a ≤ ((43/160 : ℚ) : ℝ)) (h881 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h914 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h915 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h916 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h917 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B004.c99_pos (not_le.mp h747).le h880 (not_le.mp h881).le h917
      · -- right
        exact CKLaneC2R.Cells.S01.B005.c100_pos (not_le.mp h747).le h880 (not_le.mp h917).le h916
    · -- right
      by_cases h918 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B005.c103_pos (not_le.mp h747).le h880 (not_le.mp h916).le h918
      · -- right
        exact CKLaneC2R.Cells.S01.B005.c104_pos (not_le.mp h747).le h880 (not_le.mp h918).le h915
  · -- right
    by_cases h919 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h920 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B006.c127_pos (not_le.mp h747).le h880 (not_le.mp h915).le h920
      · -- right
        exact CKLaneC2R.Cells.S01.B006.c129_pos (not_le.mp h747).le h880 (not_le.mp h920).le h919
    · -- right
      by_cases h921 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B006.c135_pos (not_le.mp h747).le h880 (not_le.mp h919).le h921
      · -- right
        exact CKLaneC2R.Cells.S01.B006.c137_pos (not_le.mp h747).le h880 (not_le.mp h921).le h914

theorem strip1_s095 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : ¬ (a ≤ ((21/80 : ℚ) : ℝ))) (h880 : a ≤ ((43/160 : ℚ) : ℝ)) (h881 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h914 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h922 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h923 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h924 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B008.c160_pos (not_le.mp h747).le h880 (not_le.mp h914).le h924
    · -- right
      exact CKLaneC2R.Cells.S01.B008.c162_pos (not_le.mp h747).le h880 (not_le.mp h924).le h923
  · -- right
    by_cases h925 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B008.c164_pos (not_le.mp h747).le h880 (not_le.mp h923).le h925
    · -- right
      by_cases h926 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B028.c566_pos (not_le.mp h747).le h880 (not_le.mp h925).le h926
      · -- right
        exact CKLaneC2R.Cells.S01.B028.c567_pos (not_le.mp h747).le h880 (not_le.mp h926).le h922

end CKLaneC2R.CompactCover


