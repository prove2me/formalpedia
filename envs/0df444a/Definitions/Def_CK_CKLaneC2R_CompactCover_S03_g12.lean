-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g12
-- name    : CK_CKLaneC2R_CompactCover_S03_g12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T13:04:02.379989+00:00
-- url     : https://prove2.me/theorems/3737f1e3-2815-4fbc-a124-4fce0b32a73c
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

import Definitions.Def_CK_CKLaneC2R_Cells_S03_B007
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B019
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B020

namespace CKLaneC2R.CompactCover

theorem strip3_s018 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((3/5 : ℚ) : ℝ)) (h1 : ¬ (a ≤ ((11/20 : ℚ) : ℝ))) (h119 : ¬ (a ≤ ((23/40 : ℚ) : ℝ))) (h172 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h196 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h204 : z ≤ ((7079/8000 : ℚ) : ℝ)
  · -- left
    by_cases h205 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h206 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B007.c151_pos (not_le.mp h119).le h0 (not_le.mp h196).le h206
      · -- right
        exact CKLaneC2R.Cells.S03.B007.c152_pos (not_le.mp h119).le h0 (not_le.mp h206).le h205
    · -- right
      by_cases h207 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B007.c154_pos (not_le.mp h119).le h0 (not_le.mp h205).le h207
      · -- right
        exact CKLaneC2R.Cells.S03.B007.c155_pos (not_le.mp h119).le h0 (not_le.mp h207).le h204
  · -- right
    by_cases h208 : z ≤ ((15071/16000 : ℚ) : ℝ)
    · -- left
      by_cases h209 : a ≤ ((47/80 : ℚ) : ℝ)
      · -- left
        by_cases h210 : z ≤ ((29229/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B013.c270_pos (not_le.mp h119).le h209 (not_le.mp h204).le h210
        · -- right
          exact CKLaneC2R.Cells.S03.B013.c272_pos (not_le.mp h119).le h209 (not_le.mp h210).le h208
      · -- right
        by_cases h211 : z ≤ ((29229/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B013.c271_pos (not_le.mp h209).le h0 (not_le.mp h204).le h211
        · -- right
          exact CKLaneC2R.Cells.S03.B013.c273_pos (not_le.mp h209).le h0 (not_le.mp h211).le h208
    · -- right
      by_cases h212 : z ≤ ((6211/6400 : ℚ) : ℝ)
      · -- left
        by_cases h213 : z ≤ ((61197/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B014.c292_pos (not_le.mp h119).le h0 (not_le.mp h208).le h213
        · -- right
          exact CKLaneC2R.Cells.S03.B014.c293_pos (not_le.mp h119).le h0 (not_le.mp h213).le h212
      · -- right
        by_cases h214 : z ≤ ((63023/64000 : ℚ) : ℝ)
        · -- left
          by_cases h215 : z ≤ ((125133/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B017.c352_pos (not_le.mp h119).le h0 (not_le.mp h212).le h215
          · -- right
            exact CKLaneC2R.Cells.S03.B017.c353_pos (not_le.mp h119).le h0 (not_le.mp h215).le h214
        · -- right
          by_cases h216 : z ≤ ((126959/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B018.c362_pos (not_le.mp h119).le h0 (not_le.mp h214).le h216
          · -- right
            by_cases h217 : z ≤ ((254831/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S03.B018.c376_pos (not_le.mp h119).le h0 (not_le.mp h216).le h217
            · -- right
              by_cases h218 : z ≤ ((20423/20480 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S03.B019.c384_pos (not_le.mp h119).le h0 (not_le.mp h217).le h218
              · -- right
                by_cases h219 : a ≤ ((47/80 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S03.B019.c399_pos (not_le.mp h119).le h219 (not_le.mp h218).le hz2
                · -- right
                  exact CKLaneC2R.Cells.S03.B020.c400_pos (not_le.mp h219).le h0 (not_le.mp h218).le hz2

end CKLaneC2R.CompactCover


