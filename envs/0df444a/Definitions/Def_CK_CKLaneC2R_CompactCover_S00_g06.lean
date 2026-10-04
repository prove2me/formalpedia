-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S00_g06
-- name    : CK_CKLaneC2R_CompactCover_S00_g06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T22:30:23.046835+00:00
-- url     : https://prove2.me/theorems/544cd534-9e31-40b2-aa4f-5e837bb73a57
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

import Definitions.Def_CK_CKLaneC2R_Cells_S00_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B020
import Definitions.Def_CK_CKLaneC2R_Cells_S00_B021

namespace CKLaneC2R.CompactCover

theorem strip0_s008 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((7/40 : ℚ) : ℝ)) (h1 : a ≤ ((13/80 : ℚ) : ℝ)) (h2 : a ≤ ((5/32 : ℚ) : ℝ)) (h3 : a ≤ ((49/320 : ℚ) : ℝ)) (h4 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h78 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h79 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h80 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h81 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        by_cases h82 : z ≤ ((35633/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B017.c345_pos ha1 h3 (not_le.mp h4).le h82
        · -- right
          exact CKLaneC2R.Cells.S00.B017.c346_pos ha1 h3 (not_le.mp h82).le h81
      · -- right
        by_cases h83 : z ≤ ((37459/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B017.c349_pos ha1 h3 (not_le.mp h81).le h83
        · -- right
          exact CKLaneC2R.Cells.S00.B017.c350_pos ha1 h3 (not_le.mp h83).le h80
    · -- right
      by_cases h84 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        by_cases h85 : z ≤ ((7857/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B018.c361_pos ha1 h3 (not_le.mp h80).le h85
        · -- right
          exact CKLaneC2R.Cells.S00.B018.c362_pos ha1 h3 (not_le.mp h85).le h84
      · -- right
        by_cases h86 : z ≤ ((41111/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B018.c365_pos ha1 h3 (not_le.mp h84).le h86
        · -- right
          exact CKLaneC2R.Cells.S00.B018.c366_pos ha1 h3 (not_le.mp h86).le h79
  · -- right
    by_cases h87 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h88 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        by_cases h89 : z ≤ ((42937/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B020.c409_pos ha1 h3 (not_le.mp h79).le h89
        · -- right
          exact CKLaneC2R.Cells.S00.B020.c410_pos ha1 h3 (not_le.mp h89).le h88
      · -- right
        by_cases h90 : z ≤ ((44763/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B020.c413_pos ha1 h3 (not_le.mp h88).le h90
        · -- right
          exact CKLaneC2R.Cells.S00.B020.c414_pos ha1 h3 (not_le.mp h90).le h87
    · -- right
      by_cases h91 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        by_cases h92 : z ≤ ((46589/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B021.c425_pos ha1 h3 (not_le.mp h87).le h92
        · -- right
          exact CKLaneC2R.Cells.S00.B021.c426_pos ha1 h3 (not_le.mp h92).le h91
      · -- right
        by_cases h93 : z ≤ ((9683/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S00.B021.c429_pos ha1 h3 (not_le.mp h91).le h93
        · -- right
          exact CKLaneC2R.Cells.S00.B021.c430_pos ha1 h3 (not_le.mp h93).le h78

end CKLaneC2R.CompactCover


