-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g02
-- name    : CK_CKLaneC2R_CompactCover_S03_g02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T09:29:23.731329+00:00
-- url     : https://prove2.me/theorems/cea0c77d-3a6f-45bf-aa24-3f437797acf4
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

import Definitions.Def_CK_CKLaneC2R_Cells_S03_B012
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B019

namespace CKLaneC2R.CompactCover

theorem strip3_s004 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((3/5 : ℚ) : ℝ)) (h1 : a ≤ ((11/20 : ℚ) : ℝ)) (h2 : a ≤ ((21/40 : ℚ) : ℝ)) (h3 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h32 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h40 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h48 : z ≤ ((15071/16000 : ℚ) : ℝ)
  · -- left
    by_cases h49 : a ≤ ((41/80 : ℚ) : ℝ)
    · -- left
      by_cases h50 : z ≤ ((29229/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B012.c258_pos ha1 h49 (not_le.mp h40).le h50
      · -- right
        exact CKLaneC2R.Cells.S03.B013.c260_pos ha1 h49 (not_le.mp h50).le h48
    · -- right
      by_cases h51 : z ≤ ((29229/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B012.c259_pos (not_le.mp h49).le h2 (not_le.mp h40).le h51
      · -- right
        exact CKLaneC2R.Cells.S03.B013.c261_pos (not_le.mp h49).le h2 (not_le.mp h51).le h48
  · -- right
    by_cases h52 : z ≤ ((6211/6400 : ℚ) : ℝ)
    · -- left
      by_cases h53 : a ≤ ((41/80 : ℚ) : ℝ)
      · -- left
        by_cases h54 : z ≤ ((61197/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B016.c338_pos ha1 h53 (not_le.mp h48).le h54
        · -- right
          exact CKLaneC2R.Cells.S03.B017.c340_pos ha1 h53 (not_le.mp h54).le h52
      · -- right
        by_cases h55 : z ≤ ((61197/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B016.c339_pos (not_le.mp h53).le h2 (not_le.mp h48).le h55
        · -- right
          exact CKLaneC2R.Cells.S03.B017.c341_pos (not_le.mp h53).le h2 (not_le.mp h55).le h52
    · -- right
      by_cases h56 : z ≤ ((63023/64000 : ℚ) : ℝ)
      · -- left
        by_cases h57 : z ≤ ((125133/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B017.c346_pos ha1 h2 (not_le.mp h52).le h57
        · -- right
          exact CKLaneC2R.Cells.S03.B017.c347_pos ha1 h2 (not_le.mp h57).le h56
      · -- right
        by_cases h58 : z ≤ ((126959/128000 : ℚ) : ℝ)
        · -- left
          by_cases h59 : a ≤ ((41/80 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B018.c367_pos ha1 h59 (not_le.mp h56).le h58
          · -- right
            exact CKLaneC2R.Cells.S03.B018.c368_pos (not_le.mp h59).le h2 (not_le.mp h56).le h58
        · -- right
          by_cases h60 : z ≤ ((254831/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B018.c373_pos ha1 h2 (not_le.mp h58).le h60
          · -- right
            by_cases h61 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S03.B019.c381_pos ha1 h2 (not_le.mp h60).le h61
            · -- right
              by_cases h62 : a ≤ ((41/80 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S03.B019.c393_pos ha1 h62 (not_le.mp h61).le hz2
              · -- right
                exact CKLaneC2R.Cells.S03.B019.c394_pos (not_le.mp h62).le h2 (not_le.mp h61).le hz2

end CKLaneC2R.CompactCover


