-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S01_g20
-- name    : CK_CKLaneC2R_CompactCover_S01_g20
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T20:02:32.205245+00:00
-- url     : https://prove2.me/theorems/8cb4f1fb-5c45-4f0f-9cbc-5379dca4b15c
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

import Definitions.Def_CK_CKLaneC2R_Cells_S01_B034
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B035
import Definitions.Def_CK_CKLaneC2R_Cells_S01_B009

namespace CKLaneC2R.CompactCover

theorem strip1_s026 {a z : ℝ} (ha1 : ((1/5 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((1/4 : ℚ) : ℝ)) (h1 : a ≤ ((9/40 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((17/80 : ℚ) : ℝ))) (h224 : a ≤ ((7/32 : ℚ) : ℝ)) (h225 : z ≤ ((217/400 : ℚ) : ℝ)) (h226 : ¬ (a ≤ ((69/320 : ℚ) : ℝ))) (h254 : z ≤ ((1257/4000 : ℚ) : ℝ)) (h255 : ¬ (z ≤ ((1601/8000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h267 : z ≤ ((823/3200 : ℚ) : ℝ)
  · -- left
    by_cases h268 : z ≤ ((7317/32000 : ℚ) : ℝ)
    · -- left
      by_cases h269 : z ≤ ((13721/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B034.c696_pos (not_le.mp h226).le h224 (not_le.mp h255).le h269
      · -- right
        exact CKLaneC2R.Cells.S01.B034.c698_pos (not_le.mp h226).le h224 (not_le.mp h269).le h268
    · -- right
      by_cases h270 : z ≤ ((15547/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B035.c705_pos (not_le.mp h226).le h224 (not_le.mp h268).le h270
      · -- right
        exact CKLaneC2R.Cells.S01.B035.c706_pos (not_le.mp h226).le h224 (not_le.mp h270).le h267
  · -- right
    by_cases h271 : z ≤ ((9143/32000 : ℚ) : ℝ)
    · -- left
      by_cases h272 : z ≤ ((17373/64000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S01.B035.c713_pos (not_le.mp h226).le h224 (not_le.mp h267).le h272
      · -- right
        exact CKLaneC2R.Cells.S01.B035.c714_pos (not_le.mp h226).le h224 (not_le.mp h272).le h271
    · -- right
      exact CKLaneC2R.Cells.S01.B009.c181_pos (not_le.mp h226).le h224 (not_le.mp h271).le h254

end CKLaneC2R.CompactCover


