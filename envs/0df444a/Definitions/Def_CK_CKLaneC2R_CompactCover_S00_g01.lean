-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g01
-- name    : CK_CKLaneC2R_CompactCover_S00_g01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T09:18:23.416069+00:00
-- url     : https://prove2.me/theorems/5a286bfb-5d30-494d-aa92-9fef55442d87
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B055
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B056
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B033
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B035
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B037

namespace CKLaneC2R.CompactCover

theorem strip0_s001 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : a ≤ ((49/320 : ℚ) : ℝ)) (h4 : z ≤ ((217/400 : ℚ) : ℝ)) (h5 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h6 : a ≤ ((97/640 : ℚ) : ℝ)) (h7 : z ≤ ((1601/8000 : ℚ) : ℝ)) (h8 : ¬ (z ≤ ((2289/16000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h19 : z ≤ ((5491/32000 : ℚ) : ℝ)
  · -- left
    by_cases h20 : z ≤ ((10069/64000 : ℚ) : ℝ)
    · -- left
      by_cases h21 : z ≤ ((769/5120 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B055.c1108_pos ha1 h6 (not_le.mp h8).le h21
      · -- right
        exact CKLaneC2R.Cells.S00.B055.c1109_pos ha1 h6 (not_le.mp h21).le h20
    · -- right
      by_cases h22 : z ≤ ((21051/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B055.c1112_pos ha1 h6 (not_le.mp h20).le h22
      · -- right
        exact CKLaneC2R.Cells.S00.B055.c1113_pos ha1 h6 (not_le.mp h22).le h19
  · -- right
    by_cases h23 : z ≤ ((2379/12800 : ℚ) : ℝ)
    · -- left
      by_cases h24 : z ≤ ((22877/128000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B056.c1124_pos ha1 h6 (not_le.mp h19).le h24
      · -- right
        exact CKLaneC2R.Cells.S00.B056.c1125_pos ha1 h6 (not_le.mp h24).le h23
    · -- right
      exact CKLaneC2R.Cells.S00.B033.c672_pos ha1 h6 (not_le.mp h23).le h7

theorem strip0_s002 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : a ≤ ((49/320 : ℚ) : ℝ)) (h4 : z ≤ ((217/400 : ℚ) : ℝ)) (h5 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h6 : a ≤ ((97/640 : ℚ) : ℝ)) (h7 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h25 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h26 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h27 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B035.c709_pos ha1 h6 (not_le.mp h7).le h27
      · -- right
        exact CKLaneC2R.Cells.S00.B035.c711_pos ha1 h6 (not_le.mp h27).le h26
    · -- right
      by_cases h28 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B035.c717_pos ha1 h6 (not_le.mp h26).le h28
      · -- right
        exact CKLaneC2R.Cells.S00.B035.c719_pos ha1 h6 (not_le.mp h28).le h25
  · -- right
    by_cases h29 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h30 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B037.c741_pos ha1 h6 (not_le.mp h25).le h30
      · -- right
        exact CKLaneC2R.Cells.S00.B037.c743_pos ha1 h6 (not_le.mp h30).le h29
    · -- right
      by_cases h31 : z ≤ ((19199/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S00.B037.c749_pos ha1 h6 (not_le.mp h29).le h31
      · -- right
        exact CKLaneC2R.Cells.S00.B037.c751_pos ha1 h6 (not_le.mp h31).le h5

end CKLaneC2R.CompactCover


