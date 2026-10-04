-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g67
-- name    : CK_CKLaneC2R_CompactCover_S01_g67
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T23:01:19.868184+00:00
-- url     : https://prove2.me/theorems/cd05edda-5340-45d1-91bd-acec6c7aee70
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B029
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B030
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B045
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B046
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B055
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B056
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B058
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B059

namespace CKLaneC2R.CompactCover

theorem strip1_s096 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1/4 : ℚ) : ℝ))) (h746 : a ≤ ((11/40 : ℚ) : ℝ)) (h747 : ¬ (a ≤ ((21/80 : ℚ) : ℝ))) (h880 : a ≤ ((43/160 : ℚ) : ℝ)) (h881 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h914 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h922 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h927 : z ≤ ((15071/16000 : ℚ) : ℝ)
  · -- left
    by_cases h928 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      by_cases h929 : z ≤ ((11509/12800 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B029.c595_pos (not_le.mp h747).le h880 (not_le.mp h922).le h929
      · -- right
        exact CKLaneC2R.Cells.S01.B029.c596_pos (not_le.mp h747).le h880 (not_le.mp h929).le h928
    · -- right
      by_cases h930 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B030.c603_pos (not_le.mp h747).le h880 (not_le.mp h928).le h930
      · -- right
        exact CKLaneC2R.Cells.S01.B030.c605_pos (not_le.mp h747).le h880 (not_le.mp h930).le h927
  · -- right
    by_cases h931 : z ≤ ((6211/6400 : ℚ) : ℝ)
    · -- left
      by_cases h932 : z ≤ ((61197/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B031.c624_pos (not_le.mp h747).le h880 (not_le.mp h927).le h932
      · -- right
        by_cases h933 : z ≤ ((123307/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B045.c919_pos (not_le.mp h747).le h880 (not_le.mp h932).le h933
        · -- right
          exact CKLaneC2R.Cells.S01.B046.c920_pos (not_le.mp h747).le h880 (not_le.mp h933).le h931
    · -- right
      by_cases h934 : z ≤ ((63023/64000 : ℚ) : ℝ)
      · -- left
        by_cases h935 : z ≤ ((125133/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B046.c937_pos (not_le.mp h747).le h880 (not_le.mp h931).le h935
        · -- right
          exact CKLaneC2R.Cells.S01.B046.c939_pos (not_le.mp h747).le h880 (not_le.mp h935).le h934
      · -- right
        by_cases h936 : z ≤ ((126959/128000 : ℚ) : ℝ)
        · -- left
          by_cases h937 : z ≤ ((50601/51200 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B055.c1112_pos (not_le.mp h747).le h880 (not_le.mp h934).le h937
          · -- right
            exact CKLaneC2R.Cells.S01.B055.c1114_pos (not_le.mp h747).le h880 (not_le.mp h937).le h936
        · -- right
          by_cases h938 : z ≤ ((254831/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S01.B056.c1122_pos (not_le.mp h747).le h880 (not_le.mp h936).le h938
          · -- right
            by_cases h939 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S01.B058.c1165_pos (not_le.mp h747).le h880 (not_le.mp h938).le h939
            · -- right
              by_cases h940 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S01.B059.c1194_pos (not_le.mp h747).le h880 (not_le.mp h939).le h940
              · -- right
                exact CKLaneC2R.Cells.S01.B059.c1196_pos (not_le.mp h747).le h880 (not_le.mp h940).le hz2

end CKLaneC2R.CompactCover


