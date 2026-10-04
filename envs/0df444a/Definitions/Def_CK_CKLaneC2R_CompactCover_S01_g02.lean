-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g02
-- name    : CK_CKLaneC2R_CompactCover_S01_g02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T01:54:56.411513+00:00
-- url     : https://prove2.me/theorems/4515c154-9468-4c92-9700-d0fd6df0c4cf
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.CompactCover.S01 (proof part of strip1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.CompactCover.S01 (proof part of strip1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/CompactCover/S01 (proof part of strip1).lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B039
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B010
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B011
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B012

namespace CKLaneC2R.CompactCover

theorem strip1_s002 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : a ≤ ((17/80 : ℚ) : ℝ)) (h3 : a ≤ ((33/160 : ℚ) : ℝ)) (h4 : z ≤ ((217/400 : ℚ) : ℝ)) (h5 : a ≤ ((13/64 : ℚ) : ℝ)) (h6 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h28 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h29 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h30 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        by_cases h31 : z ≤ ((841/2560 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S01.B039.c782_pos ha1 h5 (not_le.mp h6).le h31
        · -- right
          exact CKLaneC2R.Cells.S01.B039.c783_pos ha1 h5 (not_le.mp h31).le h30
      · -- right
        exact CKLaneC2R.Cells.S01.B010.c208_pos ha1 h5 (not_le.mp h30).le h29
    · -- right
      by_cases h32 : z ≤ ((2559/6400 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B010.c214_pos ha1 h5 (not_le.mp h29).le h32
      · -- right
        exact CKLaneC2R.Cells.S01.B010.c216_pos ha1 h5 (not_le.mp h32).le h28
  · -- right
    by_cases h33 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h34 : z ≤ ((14621/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B011.c238_pos ha1 h5 (not_le.mp h28).le h34
      · -- right
        exact CKLaneC2R.Cells.S01.B012.c240_pos ha1 h5 (not_le.mp h34).le h33
    · -- right
      by_cases h35 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B012.c246_pos ha1 h5 (not_le.mp h33).le h35
      · -- right
        exact CKLaneC2R.Cells.S01.B012.c248_pos ha1 h5 (not_le.mp h35).le h4

end CKLaneC2R.CompactCover


