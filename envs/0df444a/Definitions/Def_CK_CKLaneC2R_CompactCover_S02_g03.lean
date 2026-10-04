-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g03
-- name    : CK_CKLaneC2R_CompactCover_S02_g03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T14:52:59.20069+00:00
-- url     : https://prove2.me/theorems/dd43c278-995d-436b-8c5a-767ae6dd5504
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B022
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B023
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B024

namespace CKLaneC2R.CompactCover

theorem strip2_s003 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : a ≤ ((13/40 : ℚ) : ℝ)) (h3 : a ≤ ((5/16 : ℚ) : ℝ)) (h4 : z ≤ ((217/400 : ℚ) : ℝ)) (h5 : ¬ (a ≤ ((49/160 : ℚ) : ℝ))) (h28 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h43 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h44 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h45 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B016.c321_pos (not_le.mp h5).le h3 (not_le.mp h28).le h45
      · -- right
        exact CKLaneC2R.Cells.S02.B016.c323_pos (not_le.mp h5).le h3 (not_le.mp h45).le h44
    · -- right
      by_cases h46 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B016.c329_pos (not_le.mp h5).le h3 (not_le.mp h44).le h46
      · -- right
        exact CKLaneC2R.Cells.S02.B016.c331_pos (not_le.mp h5).le h3 (not_le.mp h46).le h43
  · -- right
    by_cases h47 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h48 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B016.c337_pos (not_le.mp h5).le h3 (not_le.mp h43).le h48
      · -- right
        exact CKLaneC2R.Cells.S02.B016.c339_pos (not_le.mp h5).le h3 (not_le.mp h48).le h47
    · -- right
      by_cases h49 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B017.c345_pos (not_le.mp h5).le h3 (not_le.mp h47).le h49
      · -- right
        exact CKLaneC2R.Cells.S02.B017.c347_pos (not_le.mp h5).le h3 (not_le.mp h49).le h4

theorem strip2_s004 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : a ≤ ((13/40 : ℚ) : ℝ)) (h3 : a ≤ ((5/16 : ℚ) : ℝ)) (h4 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h50 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h51 : a ≤ ((49/160 : ℚ) : ℝ)
  · -- left
    by_cases h52 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h53 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h54 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B022.c457_pos ha1 h51 (not_le.mp h4).le h54
        · -- right
          exact CKLaneC2R.Cells.S02.B022.c459_pos ha1 h51 (not_le.mp h54).le h53
      · -- right
        by_cases h55 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B023.c465_pos ha1 h51 (not_le.mp h53).le h55
        · -- right
          exact CKLaneC2R.Cells.S02.B023.c467_pos ha1 h51 (not_le.mp h55).le h52
    · -- right
      by_cases h56 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        by_cases h57 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B023.c473_pos ha1 h51 (not_le.mp h52).le h57
        · -- right
          exact CKLaneC2R.Cells.S02.B023.c475_pos ha1 h51 (not_le.mp h57).le h56
      · -- right
        by_cases h58 : z ≤ ((23751/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B024.c481_pos ha1 h51 (not_le.mp h56).le h58
        · -- right
          exact CKLaneC2R.Cells.S02.B024.c483_pos ha1 h51 (not_le.mp h58).le h50
  · -- right
    by_cases h59 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h60 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        by_cases h61 : z ≤ ((18273/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B022.c458_pos (not_le.mp h51).le h3 (not_le.mp h4).le h61
        · -- right
          exact CKLaneC2R.Cells.S02.B023.c460_pos (not_le.mp h51).le h3 (not_le.mp h61).le h60
      · -- right
        by_cases h62 : z ≤ ((20099/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B023.c466_pos (not_le.mp h51).le h3 (not_le.mp h60).le h62
        · -- right
          exact CKLaneC2R.Cells.S02.B023.c468_pos (not_le.mp h51).le h3 (not_le.mp h62).le h59
    · -- right
      by_cases h63 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        by_cases h64 : z ≤ ((877/1280 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B023.c474_pos (not_le.mp h51).le h3 (not_le.mp h59).le h64
        · -- right
          exact CKLaneC2R.Cells.S02.B023.c476_pos (not_le.mp h51).le h3 (not_le.mp h64).le h63
      · -- right
        by_cases h65 : z ≤ ((23751/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B024.c482_pos (not_le.mp h51).le h3 (not_le.mp h63).le h65
        · -- right
          exact CKLaneC2R.Cells.S02.B024.c484_pos (not_le.mp h51).le h3 (not_le.mp h65).le h50

end CKLaneC2R.CompactCover


