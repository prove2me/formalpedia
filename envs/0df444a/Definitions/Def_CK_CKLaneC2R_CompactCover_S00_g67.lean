-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g67
-- name    : CK_CKLaneC2R_CompactCover_S00_g67
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T00:33:27.190191+00:00
-- url     : https://prove2.me/theorems/d609c194-e98a-4fcd-b182-3bf393d1acee
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B066
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B067
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B071
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B073
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B075

namespace CKLaneC2R.CompactCover

theorem strip0_s081 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((13/80 : ℚ) : ℝ))) (h481 : ¬ (a ≤ ((27/160 : ℚ) : ℝ))) (h693 : ¬ (a ≤ ((11/64 : ℚ) : ℝ))) (h794 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h845 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h861 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h869 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h875 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h879 : z ≤ ((63023/64000 : ℚ) : ℝ)
  · -- left
    by_cases h880 : z ≤ ((125133/128000 : ℚ) : ℝ)
    · -- left
      by_cases h881 : z ≤ ((249353/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B066.c1321_pos (not_le.mp h693).le h0 (not_le.mp h875).le h881
      · -- right
        exact CKLaneC2R.Cells.S00.B066.c1322_pos (not_le.mp h693).le h0 (not_le.mp h881).le h880
    · -- right
      by_cases h882 : z ≤ ((251179/256000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B066.c1328_pos (not_le.mp h693).le h0 (not_le.mp h880).le h882
      · -- right
        exact CKLaneC2R.Cells.S00.B066.c1330_pos (not_le.mp h693).le h0 (not_le.mp h882).le h879
  · -- right
    by_cases h883 : z ≤ ((126959/128000 : ℚ) : ℝ)
    · -- left
      by_cases h884 : z ≤ ((50601/51200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B067.c1349_pos (not_le.mp h693).le h0 (not_le.mp h879).le h884
      · -- right
        exact CKLaneC2R.Cells.S00.B067.c1350_pos (not_le.mp h693).le h0 (not_le.mp h884).le h883
    · -- right
      by_cases h885 : z ≤ ((254831/256000 : ℚ) : ℝ)
      · -- left
        by_cases h886 : z ≤ ((508749/512000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B071.c1433_pos (not_le.mp h693).le h0 (not_le.mp h883).le h886
        · -- right
          exact CKLaneC2R.Cells.S00.B071.c1435_pos (not_le.mp h693).le h0 (not_le.mp h886).le h885
      · -- right
        by_cases h887 : z ≤ ((20423/20480 : ℚ) : ℝ)
        · -- left
          by_cases h888 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B073.c1470_pos (not_le.mp h693).le h0 (not_le.mp h885).le h888
          · -- right
            exact CKLaneC2R.Cells.S00.B073.c1471_pos (not_le.mp h693).le h0 (not_le.mp h888).le h887
        · -- right
          by_cases h889 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S00.B073.c1479_pos (not_le.mp h693).le h0 (not_le.mp h887).le h889
          · -- right
            by_cases h890 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S00.B075.c1504_pos (not_le.mp h693).le h0 (not_le.mp h889).le h890
            · -- right
              exact CKLaneC2R.Cells.S00.B075.c1505_pos (not_le.mp h693).le h0 (not_le.mp h890).le hz2

end CKLaneC2R.CompactCover


