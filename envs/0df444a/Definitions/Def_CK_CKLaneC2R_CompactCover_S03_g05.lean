-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g05
-- name    : CK_CKLaneC2R_CompactCover_S03_g05
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T03:36:39.888351+00:00
-- url     : https://prove2.me/theorems/fd1565b6-a72f-47ed-8e47-fc45e8ef92f6
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

import Definitions.Def_CK_CKLaneC2R_Cells_S03_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B019

namespace CKLaneC2R.CompactCover

theorem strip3_s009 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((3/5 : ℚ) : ℝ)) (h1 : a ≤ ((11/20 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((21/40 : ℚ) : ℝ))) (h63 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h91 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h99 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h105 : z ≤ ((15071/16000 : ℚ) : ℝ)
  · -- left
    by_cases h106 : a ≤ ((43/80 : ℚ) : ℝ)
    · -- left
      by_cases h107 : z ≤ ((29229/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B013.c262_pos (not_le.mp h2).le h106 (not_le.mp h99).le h107
      · -- right
        exact CKLaneC2R.Cells.S03.B013.c264_pos (not_le.mp h2).le h106 (not_le.mp h107).le h105
    · -- right
      by_cases h108 : z ≤ ((29229/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B013.c263_pos (not_le.mp h106).le h1 (not_le.mp h99).le h108
      · -- right
        exact CKLaneC2R.Cells.S03.B013.c265_pos (not_le.mp h106).le h1 (not_le.mp h108).le h105
  · -- right
    by_cases h109 : z ≤ ((6211/6400 : ℚ) : ℝ)
    · -- left
      by_cases h110 : z ≤ ((61197/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B014.c290_pos (not_le.mp h2).le h1 (not_le.mp h105).le h110
      · -- right
        by_cases h111 : a ≤ ((43/80 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B017.c342_pos (not_le.mp h2).le h111 (not_le.mp h110).le h109
        · -- right
          exact CKLaneC2R.Cells.S03.B017.c343_pos (not_le.mp h111).le h1 (not_le.mp h110).le h109
    · -- right
      by_cases h112 : z ≤ ((63023/64000 : ℚ) : ℝ)
      · -- left
        by_cases h113 : z ≤ ((125133/128000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B017.c348_pos (not_le.mp h2).le h1 (not_le.mp h109).le h113
        · -- right
          exact CKLaneC2R.Cells.S03.B017.c349_pos (not_le.mp h2).le h1 (not_le.mp h113).le h112
      · -- right
        by_cases h114 : z ≤ ((126959/128000 : ℚ) : ℝ)
        · -- left
          by_cases h115 : a ≤ ((43/80 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B018.c369_pos (not_le.mp h2).le h115 (not_le.mp h112).le h114
          · -- right
            exact CKLaneC2R.Cells.S03.B018.c370_pos (not_le.mp h115).le h1 (not_le.mp h112).le h114
        · -- right
          by_cases h116 : z ≤ ((254831/256000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B018.c374_pos (not_le.mp h2).le h1 (not_le.mp h114).le h116
          · -- right
            by_cases h117 : z ≤ ((20423/20480 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S03.B019.c382_pos (not_le.mp h2).le h1 (not_le.mp h116).le h117
            · -- right
              by_cases h118 : a ≤ ((43/80 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S03.B019.c395_pos (not_le.mp h2).le h118 (not_le.mp h117).le hz2
              · -- right
                exact CKLaneC2R.Cells.S03.B019.c396_pos (not_le.mp h118).le h1 (not_le.mp h117).le hz2

end CKLaneC2R.CompactCover


