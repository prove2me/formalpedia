-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g02
-- name    : CK_CKLaneC2R_CompactCover_S02_g02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T02:36:37.579378+00:00
-- url     : https://prove2.me/theorems/c0067a85-3e40-409c-aa85-00f9a8d125f2
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B037
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B038
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B029
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B031
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B014

namespace CKLaneC2R.CompactCover

theorem strip2_s002 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : a ≤ ((13/40 : ℚ) : ℝ)) (h3 : a ≤ ((5/16 : ℚ) : ℝ)) (h4 : z ≤ ((217/400 : ℚ) : ℝ)) (h5 : ¬ (a ≤ ((49/160 : ℚ) : ℝ))) (h28 : z ≤ ((1257/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h29 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h30 : z ≤ ((2289/16000 : ℚ) : ℝ)
    · -- left
      by_cases h31 : z ≤ ((733/6400 : ℚ) : ℝ)
      · -- left
        by_cases h32 : z ≤ ((6417/64000 : ℚ) : ℝ)
        · -- left
          by_cases h33 : z ≤ ((11921/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B037.c757_pos (not_le.mp h5).le h3 hz1 h33
          · -- right
            exact CKLaneC2R.Cells.S02.B037.c758_pos (not_le.mp h5).le h3 (not_le.mp h33).le h32
        · -- right
          by_cases h34 : z ≤ ((13747/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B038.c761_pos (not_le.mp h5).le h3 (not_le.mp h32).le h34
          · -- right
            exact CKLaneC2R.Cells.S02.B038.c762_pos (not_le.mp h5).le h3 (not_le.mp h34).le h31
      · -- right
        by_cases h35 : z ≤ ((8243/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B029.c580_pos (not_le.mp h5).le h3 (not_le.mp h31).le h35
        · -- right
          exact CKLaneC2R.Cells.S02.B029.c582_pos (not_le.mp h5).le h3 (not_le.mp h35).le h30
    · -- right
      by_cases h36 : z ≤ ((5491/32000 : ℚ) : ℝ)
      · -- left
        by_cases h37 : z ≤ ((10069/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B029.c589_pos (not_le.mp h5).le h3 (not_le.mp h30).le h37
        · -- right
          exact CKLaneC2R.Cells.S02.B029.c590_pos (not_le.mp h5).le h3 (not_le.mp h37).le h36
      · -- right
        by_cases h38 : z ≤ ((2379/12800 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B029.c593_pos (not_le.mp h5).le h3 (not_le.mp h36).le h38
        · -- right
          exact CKLaneC2R.Cells.S02.B029.c594_pos (not_le.mp h5).le h3 (not_le.mp h38).le h29
  · -- right
    by_cases h39 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h40 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        by_cases h41 : z ≤ ((13721/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B031.c631_pos (not_le.mp h5).le h3 (not_le.mp h29).le h41
        · -- right
          exact CKLaneC2R.Cells.S02.B031.c632_pos (not_le.mp h5).le h3 (not_le.mp h41).le h40
      · -- right
        exact CKLaneC2R.Cells.S02.B014.c292_pos (not_le.mp h5).le h3 (not_le.mp h40).le h39
    · -- right
      by_cases h42 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B014.c297_pos (not_le.mp h5).le h3 (not_le.mp h39).le h42
      · -- right
        exact CKLaneC2R.Cells.S02.B014.c299_pos (not_le.mp h5).le h3 (not_le.mp h42).le h28

end CKLaneC2R.CompactCover


