-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g13
-- name    : CK_CKLaneC2R_CompactCover_S05_g13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T08:07:20.100898+00:00
-- url     : https://prove2.me/theorems/e4d5b5c4-556f-4419-b227-a0fc994fb608
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B010
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B021
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B024

namespace CKLaneC2R.CompactCover

theorem strip5_s021 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : a ≤ ((3897/4000 : ℚ) : ℝ)) (h148 : a ≤ ((1539/1600 : ℚ) : ℝ)) (h149 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h159 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h165 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h172 : a ≤ ((15291/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h173 : z ≤ ((15071/16000 : ℚ) : ℝ)
  · -- left
    by_cases h174 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B010.c201_pos (not_le.mp h0).le h172 (not_le.mp h165).le h174
    · -- right
      by_cases h175 : z ≤ ((59371/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B013.c277_pos (not_le.mp h0).le h172 (not_le.mp h174).le h175
      · -- right
        exact CKLaneC2R.Cells.S05.B013.c278_pos (not_le.mp h0).le h172 (not_le.mp h175).le h173
  · -- right
    by_cases h176 : z ≤ ((6211/6400 : ℚ) : ℝ)
    · -- left
      by_cases h177 : z ≤ ((61197/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S05.B014.c290_pos (not_le.mp h0).le h172 (not_le.mp h173).le h177
      · -- right
        by_cases h178 : z ≤ ((123307/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B017.c357_pos (not_le.mp h0).le h172 (not_le.mp h177).le h178
        · -- right
          exact CKLaneC2R.Cells.S05.B017.c358_pos (not_le.mp h0).le h172 (not_le.mp h178).le h176
    · -- right
      by_cases h179 : z ≤ ((63023/64000 : ℚ) : ℝ)
      · -- left
        by_cases h180 : z ≤ ((125133/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S05.B018.c368_pos (not_le.mp h0).le h172 (not_le.mp h176).le h180
        · -- right
          exact CKLaneC2R.Cells.S05.B018.c369_pos (not_le.mp h0).le h172 (not_le.mp h180).le h179
      · -- right
        by_cases h181 : z ≤ ((126959/128000 : ℚ) : ℝ)
        · -- left
          by_cases h182 : a ≤ ((30483/32000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B021.c431_pos (not_le.mp h0).le h182 (not_le.mp h179).le h181
          · -- right
            exact CKLaneC2R.Cells.S05.B021.c432_pos (not_le.mp h182).le h172 (not_le.mp h179).le h181
        · -- right
          by_cases h183 : z ≤ ((254831/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S05.B021.c435_pos (not_le.mp h0).le h172 (not_le.mp h181).le h183
          · -- right
            by_cases h184 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S05.B024.c491_pos (not_le.mp h0).le h172 (not_le.mp h183).le h184
            · -- right
              exact CKLaneC2R.Cells.S05.B024.c492_pos (not_le.mp h0).le h172 (not_le.mp h184).le hz2

end CKLaneC2R.CompactCover


