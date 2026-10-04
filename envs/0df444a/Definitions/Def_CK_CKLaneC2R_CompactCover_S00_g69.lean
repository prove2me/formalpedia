-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g69
-- name    : CK_CKLaneC2R_CompactCover_S00_g69
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T07:23:13.92022+00:00
-- url     : https://prove2.me/theorems/66f604e7-3de1-4431-9f89-4b9f753518ce
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B043
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B044
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B045
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B010
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B011

namespace CKLaneC2R.CompactCover

theorem strip0_s083 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : a ≤ ((29/160 : ℚ) : ℝ)) (h893 : a ≤ ((57/320 : ℚ) : ℝ)) (h894 : z ≤ ((217/400 : ℚ) : ℝ)) (h895 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h896 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h897 : ¬ (z ≤ ((2289/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h912 : z ≤ ((5491/32000 : ℚ) : ℝ)
  · -- left
    by_cases h913 : z ≤ ((10069/64000 : ℚ) : ℝ)
    · -- left
      by_cases h914 : z ≤ ((769/5120 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B043.c861_pos (not_le.mp h0).le h893 (not_le.mp h897).le h914
      · -- right
        exact CKLaneC2R.Cells.S00.B043.c862_pos (not_le.mp h0).le h893 (not_le.mp h914).le h913
    · -- right
      by_cases h915 : z ≤ ((21051/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B043.c865_pos (not_le.mp h0).le h893 (not_le.mp h913).le h915
      · -- right
        exact CKLaneC2R.Cells.S00.B043.c866_pos (not_le.mp h0).le h893 (not_le.mp h915).le h912
  · -- right
    by_cases h916 : z ≤ ((2379/12800 : ℚ) : ℝ)
    · -- left
      by_cases h917 : z ≤ ((22877/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B043.c877_pos (not_le.mp h0).le h893 (not_le.mp h912).le h917
      · -- right
        exact CKLaneC2R.Cells.S00.B043.c878_pos (not_le.mp h0).le h893 (not_le.mp h917).le h916
    · -- right
      by_cases h918 : a ≤ ((113/640 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B043.c879_pos (not_le.mp h0).le h918 (not_le.mp h916).le h896
      · -- right
        exact CKLaneC2R.Cells.S00.B044.c880_pos (not_le.mp h918).le h893 (not_le.mp h916).le h896

theorem strip0_s084 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((7/40 : ℚ) : ℝ))) (h891 : a ≤ ((3/16 : ℚ) : ℝ)) (h892 : a ≤ ((29/160 : ℚ) : ℝ)) (h893 : a ≤ ((57/320 : ℚ) : ℝ)) (h894 : z ≤ ((217/400 : ℚ) : ℝ)) (h895 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h896 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h919 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h920 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h921 : a ≤ ((113/640 : ℚ) : ℝ)
      · -- left
        by_cases h922 : z ≤ ((13721/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B045.c913_pos (not_le.mp h0).le h921 (not_le.mp h896).le h922
        · -- right
          exact CKLaneC2R.Cells.S00.B045.c915_pos (not_le.mp h0).le h921 (not_le.mp h922).le h920
      · -- right
        by_cases h923 : z ≤ ((13721/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B045.c914_pos (not_le.mp h921).le h893 (not_le.mp h896).le h923
        · -- right
          exact CKLaneC2R.Cells.S00.B045.c916_pos (not_le.mp h921).le h893 (not_le.mp h923).le h920
    · -- right
      by_cases h924 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B010.c206_pos (not_le.mp h0).le h893 (not_le.mp h920).le h924
      · -- right
        exact CKLaneC2R.Cells.S00.B010.c207_pos (not_le.mp h0).le h893 (not_le.mp h924).le h919
  · -- right
    by_cases h925 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h926 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B010.c217_pos (not_le.mp h0).le h893 (not_le.mp h919).le h926
      · -- right
        exact CKLaneC2R.Cells.S00.B010.c218_pos (not_le.mp h0).le h893 (not_le.mp h926).le h925
    · -- right
      by_cases h927 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B011.c221_pos (not_le.mp h0).le h893 (not_le.mp h925).le h927
      · -- right
        exact CKLaneC2R.Cells.S00.B011.c222_pos (not_le.mp h0).le h893 (not_le.mp h927).le h895

end CKLaneC2R.CompactCover


