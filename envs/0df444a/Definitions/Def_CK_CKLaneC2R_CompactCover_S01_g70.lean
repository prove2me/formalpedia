-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g70
-- name    : CK_CKLaneC2R_CompactCover_S01_g70
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T19:12:50.416438+00:00
-- url     : https://prove2.me/theorems/75bc55d2-faf5-4cbd-b003-025e060b5fbc
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B005
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B028

namespace CKLaneC2R.CompactCover

theorem strip1_s100 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : ¬ (a ≤ ((21/80 : ℚ) : ℝ))) (h880 : ¬ (a ≤ ((43/160 : ℚ) : ℝ))) (h941 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h971 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h972 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h973 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h974 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B005.c101_pos (not_le.mp h880).le h746 (not_le.mp h941).le h974
      · -- right
        exact CKLaneC2R.Cells.S01.B005.c102_pos (not_le.mp h880).le h746 (not_le.mp h974).le h973
    · -- right
      by_cases h975 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B005.c105_pos (not_le.mp h880).le h746 (not_le.mp h973).le h975
      · -- right
        exact CKLaneC2R.Cells.S01.B005.c106_pos (not_le.mp h880).le h746 (not_le.mp h975).le h972
  · -- right
    by_cases h976 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h977 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B006.c128_pos (not_le.mp h880).le h746 (not_le.mp h972).le h977
      · -- right
        exact CKLaneC2R.Cells.S01.B006.c130_pos (not_le.mp h880).le h746 (not_le.mp h977).le h976
    · -- right
      by_cases h978 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B006.c136_pos (not_le.mp h880).le h746 (not_le.mp h976).le h978
      · -- right
        exact CKLaneC2R.Cells.S01.B006.c138_pos (not_le.mp h880).le h746 (not_le.mp h978).le h971

theorem strip1_s101 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : ¬ (a ≤ ((21/80 : ℚ) : ℝ))) (h880 : ¬ (a ≤ ((43/160 : ℚ) : ℝ))) (h941 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h971 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h979 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h980 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h981 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B008.c161_pos (not_le.mp h880).le h746 (not_le.mp h971).le h981
    · -- right
      exact CKLaneC2R.Cells.S01.B008.c163_pos (not_le.mp h880).le h746 (not_le.mp h981).le h980
  · -- right
    by_cases h982 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S01.B008.c165_pos (not_le.mp h880).le h746 (not_le.mp h980).le h982
    · -- right
      by_cases h983 : z ≤ ((55719/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B028.c568_pos (not_le.mp h880).le h746 (not_le.mp h982).le h983
      · -- right
        exact CKLaneC2R.Cells.S01.B028.c569_pos (not_le.mp h880).le h746 (not_le.mp h983).le h979

end CKLaneC2R.CompactCover


