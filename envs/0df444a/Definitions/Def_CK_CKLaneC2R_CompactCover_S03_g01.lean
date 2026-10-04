-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g01
-- name    : CK_CKLaneC2R_CompactCover_S03_g01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T21:30:32.647922+00:00
-- url     : https://prove2.me/theorems/e903f6be-4231-43d1-ac8e-862ae2ce1eed
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

import Definitions.Def_CK_CKLaneC2R_Cells_S03_B004
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B012

namespace CKLaneC2R.CompactCover

theorem strip3_s002 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((3/5 : ℚ) : ℝ)) (h1 : a ≤ ((11/20 : ℚ) : ℝ)) (h2 : a ≤ ((21/40 : ℚ) : ℝ)) (h3 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h32 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h33 : a ≤ ((41/80 : ℚ) : ℝ)
  · -- left
    by_cases h34 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h35 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B004.c83_pos ha1 h33 (not_le.mp h3).le h35
      · -- right
        exact CKLaneC2R.Cells.S03.B004.c85_pos ha1 h33 (not_le.mp h35).le h34
    · -- right
      by_cases h36 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B004.c91_pos ha1 h33 (not_le.mp h34).le h36
      · -- right
        exact CKLaneC2R.Cells.S03.B004.c93_pos ha1 h33 (not_le.mp h36).le h32
  · -- right
    by_cases h37 : z ≤ ((5253/8000 : ℚ) : ℝ)
    · -- left
      by_cases h38 : z ≤ ((9593/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B004.c84_pos (not_le.mp h33).le h2 (not_le.mp h3).le h38
      · -- right
        exact CKLaneC2R.Cells.S03.B004.c86_pos (not_le.mp h33).le h2 (not_le.mp h38).le h37
    · -- right
      by_cases h39 : z ≤ ((11419/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B004.c92_pos (not_le.mp h33).le h2 (not_le.mp h37).le h39
      · -- right
        exact CKLaneC2R.Cells.S03.B004.c94_pos (not_le.mp h33).le h2 (not_le.mp h39).le h32

theorem strip3_s003 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((3/5 : ℚ) : ℝ)) (h1 : a ≤ ((11/20 : ℚ) : ℝ)) (h2 : a ≤ ((21/40 : ℚ) : ℝ)) (h3 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h32 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h40 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h41 : a ≤ ((41/80 : ℚ) : ℝ)
  · -- left
    by_cases h42 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h43 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B012.c244_pos ha1 h41 (not_le.mp h32).le h43
      · -- right
        exact CKLaneC2R.Cells.S03.B012.c245_pos ha1 h41 (not_le.mp h43).le h42
    · -- right
      by_cases h44 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B012.c248_pos ha1 h41 (not_le.mp h42).le h44
      · -- right
        exact CKLaneC2R.Cells.S03.B012.c250_pos ha1 h41 (not_le.mp h44).le h40
  · -- right
    by_cases h45 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h46 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B012.c246_pos (not_le.mp h41).le h2 (not_le.mp h32).le h46
      · -- right
        exact CKLaneC2R.Cells.S03.B012.c247_pos (not_le.mp h41).le h2 (not_le.mp h46).le h45
    · -- right
      by_cases h47 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B012.c249_pos (not_le.mp h41).le h2 (not_le.mp h45).le h47
      · -- right
        exact CKLaneC2R.Cells.S03.B012.c251_pos (not_le.mp h41).le h2 (not_le.mp h47).le h40

end CKLaneC2R.CompactCover


