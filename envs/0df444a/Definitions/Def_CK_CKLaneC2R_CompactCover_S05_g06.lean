-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g06
-- name    : CK_CKLaneC2R_CompactCover_S05_g06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T00:32:04.856168+00:00
-- url     : https://prove2.me/theorems/9bbd6c91-0eb6-4364-8ff2-4877351bb1b8
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B008
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B009
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B012

namespace CKLaneC2R.CompactCover

theorem strip5_s010 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1899/2000 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((3699/4000 : ℚ) : ℝ))) (h69 : a ≤ ((7497/8000 : ℚ) : ℝ)) (h70 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h79 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h84 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h85 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h86 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B006.c123_pos (not_le.mp h1).le h69 (not_le.mp h79).le h86
    · -- right
      exact CKLaneC2R.Cells.S05.B006.c124_pos (not_le.mp h1).le h69 (not_le.mp h86).le h85
  · -- right
    by_cases h87 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B006.c127_pos (not_le.mp h1).le h69 (not_le.mp h85).le h87
    · -- right
      by_cases h88 : a ≤ ((2979/3200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B008.c164_pos (not_le.mp h1).le h88 (not_le.mp h87).le h84
      · -- right
        exact CKLaneC2R.Cells.S05.B008.c165_pos (not_le.mp h88).le h69 (not_le.mp h87).le h84

theorem strip5_s011 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1899/2000 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((3699/4000 : ℚ) : ℝ))) (h69 : a ≤ ((7497/8000 : ℚ) : ℝ)) (h70 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h79 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h84 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h89 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h90 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h91 : a ≤ ((2979/3200 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B009.c195_pos (not_le.mp h1).le h91 (not_le.mp h84).le h90
    · -- right
      exact CKLaneC2R.Cells.S05.B009.c196_pos (not_le.mp h91).le h69 (not_le.mp h84).le h90
  · -- right
    by_cases h92 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B009.c199_pos (not_le.mp h1).le h69 (not_le.mp h90).le h92
    · -- right
      by_cases h93 : a ≤ ((2979/3200 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B012.c247_pos (not_le.mp h1).le h93 (not_le.mp h92).le h89
      · -- right
        exact CKLaneC2R.Cells.S05.B012.c248_pos (not_le.mp h93).le h69 (not_le.mp h92).le h89

end CKLaneC2R.CompactCover


