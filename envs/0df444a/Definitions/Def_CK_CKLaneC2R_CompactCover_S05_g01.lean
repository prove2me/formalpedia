-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g01
-- name    : CK_CKLaneC2R_CompactCover_S05_g01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T19:35:21.291531+00:00
-- url     : https://prove2.me/theorems/ad8c3088-3786-4633-aba4-1daa0c257ab1
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
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B010
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B012
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B020

namespace CKLaneC2R.CompactCover

theorem strip5_s002 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1899/2000 : ℚ) : ℝ)) (h1 : a ≤ ((3699/4000 : ℚ) : ℝ)) (h2 : a ≤ ((7299/8000 : ℚ) : ℝ)) (h3 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h12 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h17 : z ≤ ((7079/8000 : ℚ) : ℝ)
  · -- left
    by_cases h18 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h19 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B005.c115_pos ha1 h2 (not_le.mp h12).le h19
      · -- right
        exact CKLaneC2R.Cells.S05.B005.c116_pos ha1 h2 (not_le.mp h19).le h18
    · -- right
      by_cases h20 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B005.c119_pos ha1 h2 (not_le.mp h18).le h20
      · -- right
        exact CKLaneC2R.Cells.S05.B006.c120_pos ha1 h2 (not_le.mp h20).le h17
  · -- right
    by_cases h21 : z ≤ ((15071/16000 : ℚ) : ℝ)
    · -- left
      by_cases h22 : z ≤ ((29229/32000 : ℚ) : ℝ)
      · -- left
        by_cases h23 : a ≤ ((14499/16000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B009.c187_pos ha1 h23 (not_le.mp h17).le h22
        · -- right
          exact CKLaneC2R.Cells.S05.B009.c188_pos (not_le.mp h23).le h2 (not_le.mp h17).le h22
      · -- right
        by_cases h24 : z ≤ ((59371/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B009.c191_pos ha1 h2 (not_le.mp h22).le h24
        · -- right
          exact CKLaneC2R.Cells.S05.B009.c192_pos ha1 h2 (not_le.mp h24).le h21
    · -- right
      by_cases h25 : z ≤ ((6211/6400 : ℚ) : ℝ)
      · -- left
        by_cases h26 : z ≤ ((61197/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B010.c200_pos ha1 h2 (not_le.mp h21).le h26
        · -- right
          by_cases h27 : a ≤ ((14499/16000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B012.c253_pos ha1 h27 (not_le.mp h26).le h25
          · -- right
            exact CKLaneC2R.Cells.S05.B012.c254_pos (not_le.mp h27).le h2 (not_le.mp h26).le h25
      · -- right
        by_cases h28 : z ≤ ((63023/64000 : ℚ) : ℝ)
        · -- left
          by_cases h29 : a ≤ ((14499/16000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B013.c267_pos ha1 h29 (not_le.mp h25).le h28
          · -- right
            exact CKLaneC2R.Cells.S05.B013.c268_pos (not_le.mp h29).le h2 (not_le.mp h25).le h28
        · -- right
          by_cases h30 : z ≤ ((126959/128000 : ℚ) : ℝ)
          · -- left
            by_cases h31 : a ≤ ((14499/16000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S05.B016.c334_pos ha1 h31 (not_le.mp h28).le h30
            · -- right
              exact CKLaneC2R.Cells.S05.B016.c335_pos (not_le.mp h31).le h2 (not_le.mp h28).le h30
          · -- right
            by_cases h32 : z ≤ ((254831/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S05.B016.c338_pos ha1 h2 (not_le.mp h30).le h32
            · -- right
              by_cases h33 : z ≤ ((20423/20480 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B020.c403_pos ha1 h2 (not_le.mp h32).le h33
              · -- right
                exact CKLaneC2R.Cells.S05.B020.c404_pos ha1 h2 (not_le.mp h33).le hz2

end CKLaneC2R.CompactCover


