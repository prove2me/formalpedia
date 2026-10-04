-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g03
-- name    : CK_CKLaneC2R_CompactCover_S05_g03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T19:21:47.945882+00:00
-- url     : https://prove2.me/theorems/c7d7e5f3-1307-484c-88d6-706d128a33e4
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B005
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B006
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B009

namespace CKLaneC2R.CompactCover

theorem strip5_s005 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1899/2000 : ℚ) : ℝ)) (h1 : a ≤ ((3699/4000 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((7299/8000 : ℚ) : ℝ))) (h34 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h43 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h48 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h49 : z ≤ ((2649/3200 : ℚ) : ℝ)
  · -- left
    by_cases h50 : z ≤ ((25577/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B005.c117_pos (not_le.mp h2).le h1 (not_le.mp h43).le h50
    · -- right
      exact CKLaneC2R.Cells.S05.B005.c118_pos (not_le.mp h2).le h1 (not_le.mp h50).le h49
  · -- right
    by_cases h51 : z ≤ ((27403/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B006.c121_pos (not_le.mp h2).le h1 (not_le.mp h49).le h51
    · -- right
      exact CKLaneC2R.Cells.S05.B006.c122_pos (not_le.mp h2).le h1 (not_le.mp h51).le h48

theorem strip5_s006 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1899/2000 : ℚ) : ℝ)) (h1 : a ≤ ((3699/4000 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((7299/8000 : ℚ) : ℝ))) (h34 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h43 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h48 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h52 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h53 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h54 : a ≤ ((14697/16000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B009.c189_pos (not_le.mp h2).le h54 (not_le.mp h48).le h53
    · -- right
      exact CKLaneC2R.Cells.S05.B009.c190_pos (not_le.mp h54).le h1 (not_le.mp h48).le h53
  · -- right
    by_cases h55 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B009.c193_pos (not_le.mp h2).le h1 (not_le.mp h53).le h55
    · -- right
      exact CKLaneC2R.Cells.S05.B009.c194_pos (not_le.mp h2).le h1 (not_le.mp h55).le h52

end CKLaneC2R.CompactCover


