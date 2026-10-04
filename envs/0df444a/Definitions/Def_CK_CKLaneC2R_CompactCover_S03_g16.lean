-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g16
-- name    : CK_CKLaneC2R_CompactCover_S03_g16
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T15:52:44.032239+00:00
-- url     : https://prove2.me/theorems/f8d65bcd-b5f4-4b37-b54c-7023e09ac216
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

import Definitions.Def_CK_CKLaneC2R_Cells_S03_B016
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B011
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B001
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B002
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B003

namespace CKLaneC2R.CompactCover

theorem strip3_s023 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((3/5 : ℚ) : ℝ))) (h220 : a ≤ ((13/20 : ℚ) : ℝ)) (h221 : ¬ (a ≤ ((5/8 : ℚ) : ℝ))) (h268 : z ≤ ((217/400 : ℚ) : ℝ)) (h269 : z ≤ ((1257/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h270 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h271 : a ≤ ((51/80 : ℚ) : ℝ)
    · -- left
      by_cases h272 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        by_cases h273 : z ≤ ((733/6400 : ℚ) : ℝ)
        · -- left
          by_cases h274 : z ≤ ((6417/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B016.c330_pos (not_le.mp h221).le h271 hz1 h274
          · -- right
            exact CKLaneC2R.Cells.S03.B016.c332_pos (not_le.mp h221).le h271 (not_le.mp h274).le h273
        · -- right
          exact CKLaneC2R.Cells.S03.B011.c222_pos (not_le.mp h221).le h271 (not_le.mp h273).le h272
      · -- right
        by_cases h275 : z ≤ ((5491/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B011.c228_pos (not_le.mp h221).le h271 (not_le.mp h272).le h275
        · -- right
          exact CKLaneC2R.Cells.S03.B011.c230_pos (not_le.mp h221).le h271 (not_le.mp h275).le h270
    · -- right
      by_cases h276 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        by_cases h277 : z ≤ ((733/6400 : ℚ) : ℝ)
        · -- left
          by_cases h278 : z ≤ ((6417/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B016.c331_pos (not_le.mp h271).le h220 hz1 h278
          · -- right
            exact CKLaneC2R.Cells.S03.B016.c333_pos (not_le.mp h271).le h220 (not_le.mp h278).le h277
        · -- right
          exact CKLaneC2R.Cells.S03.B011.c223_pos (not_le.mp h271).le h220 (not_le.mp h277).le h276
      · -- right
        by_cases h279 : z ≤ ((5491/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B011.c229_pos (not_le.mp h271).le h220 (not_le.mp h276).le h279
        · -- right
          exact CKLaneC2R.Cells.S03.B011.c231_pos (not_le.mp h271).le h220 (not_le.mp h279).le h270
  · -- right
    by_cases h280 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h281 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B001.c37_pos (not_le.mp h221).le h220 (not_le.mp h270).le h281
      · -- right
        exact CKLaneC2R.Cells.S03.B001.c38_pos (not_le.mp h221).le h220 (not_le.mp h281).le h280
    · -- right
      by_cases h282 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B002.c41_pos (not_le.mp h221).le h220 (not_le.mp h280).le h282
      · -- right
        exact CKLaneC2R.Cells.S03.B002.c42_pos (not_le.mp h221).le h220 (not_le.mp h282).le h269

theorem strip3_s024 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((3/5 : ℚ) : ℝ))) (h220 : a ≤ ((13/20 : ℚ) : ℝ)) (h221 : ¬ (a ≤ ((5/8 : ℚ) : ℝ))) (h268 : z ≤ ((217/400 : ℚ) : ℝ)) (h269 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h283 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h284 : z ≤ ((5941/16000 : ℚ) : ℝ)
    · -- left
      by_cases h285 : z ≤ ((10969/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B002.c55_pos (not_le.mp h221).le h220 (not_le.mp h269).le h285
      · -- right
        exact CKLaneC2R.Cells.S03.B002.c56_pos (not_le.mp h221).le h220 (not_le.mp h285).le h284
    · -- right
      by_cases h286 : a ≤ ((51/80 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B002.c57_pos (not_le.mp h221).le h286 (not_le.mp h284).le h283
      · -- right
        exact CKLaneC2R.Cells.S03.B002.c58_pos (not_le.mp h286).le h220 (not_le.mp h284).le h283
  · -- right
    by_cases h287 : a ≤ ((51/80 : ℚ) : ℝ)
    · -- left
      by_cases h288 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B003.c63_pos (not_le.mp h221).le h287 (not_le.mp h283).le h288
      · -- right
        exact CKLaneC2R.Cells.S03.B003.c65_pos (not_le.mp h221).le h287 (not_le.mp h288).le h268
    · -- right
      by_cases h289 : z ≤ ((7767/16000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B003.c64_pos (not_le.mp h287).le h220 (not_le.mp h283).le h289
      · -- right
        exact CKLaneC2R.Cells.S03.B003.c66_pos (not_le.mp h287).le h220 (not_le.mp h289).le h268

end CKLaneC2R.CompactCover


