-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g08
-- name    : CK_CKLaneC2R_CompactCover_S05_g08
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T20:39:40.64854+00:00
-- url     : https://prove2.me/theorems/cbee6762-eb23-4fbc-8b47-c2eb4fdfd387
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S05 (proof part of strip5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S05 (proof part of strip5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S05 (proof part of strip5).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B002
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B000
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B001
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B004

namespace CKLaneC2R.CompactCover

theorem strip5_s013 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1899/2000 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((3699/4000 : ℚ) : ℝ))) (h69 : ¬ (a ≤ ((7497/8000 : ℚ) : ℝ))) (h107 : z ≤ ((217/400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h108 : z ≤ ((1257/4000 : ℚ) : ℝ)
  · -- left
    by_cases h109 : z ≤ ((1601/8000 : ℚ) : ℝ)
    · -- left
      by_cases h110 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        by_cases h111 : z ≤ ((733/6400 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B002.c54_pos (not_le.mp h69).le h0 hz1 h111
        · -- right
          exact CKLaneC2R.Cells.S05.B002.c55_pos (not_le.mp h69).le h0 (not_le.mp h111).le h110
      · -- right
        exact CKLaneC2R.Cells.S05.B000.c3_pos (not_le.mp h69).le h0 (not_le.mp h110).le h109
    · -- right
      by_cases h112 : z ≤ ((823/3200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B000.c10_pos (not_le.mp h69).le h0 (not_le.mp h109).le h112
      · -- right
        exact CKLaneC2R.Cells.S05.B000.c11_pos (not_le.mp h69).le h0 (not_le.mp h112).le h108
  · -- right
    by_cases h113 : z ≤ ((3427/8000 : ℚ) : ℝ)
    · -- left
      by_cases h114 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B000.c17_pos (not_le.mp h69).le h0 (not_le.mp h108).le h114
      · -- right
        exact CKLaneC2R.Cells.S05.B000.c19_pos (not_le.mp h69).le h0 (not_le.mp h114).le h113
    · -- right
      by_cases h115 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B001.c25_pos (not_le.mp h69).le h0 (not_le.mp h113).le h115
      · -- right
        exact CKLaneC2R.Cells.S05.B001.c27_pos (not_le.mp h69).le h0 (not_le.mp h115).le h107

theorem strip5_s014 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1899/2000 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((3699/4000 : ℚ) : ℝ))) (h69 : ¬ (a ≤ ((7497/8000 : ℚ) : ℝ))) (h107 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h116 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h117 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h118 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B001.c39_pos (not_le.mp h69).le h0 (not_le.mp h107).le h118
    · -- right
      exact CKLaneC2R.Cells.S05.B002.c41_pos (not_le.mp h69).le h0 (not_le.mp h118).le h117
  · -- right
    by_cases h119 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B002.c45_pos (not_le.mp h69).le h0 (not_le.mp h117).le h119
    · -- right
      by_cases h120 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B004.c97_pos (not_le.mp h69).le h0 (not_le.mp h119).le h120
      · -- right
        exact CKLaneC2R.Cells.S05.B004.c98_pos (not_le.mp h69).le h0 (not_le.mp h120).le h116

end CKLaneC2R.CompactCover


