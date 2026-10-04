-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S03_g13
-- name    : CK_CKLaneC2R_CompactCover_S03_g13
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T22:30:19.34613+00:00
-- url     : https://prove2.me/theorems/56344579-383f-4cc2-9cdd-1d44e0271e0f
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
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B012
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B001
import Definitions.Def_CK_CKLaneC2R_Cells_S03_B002

namespace CKLaneC2R.CompactCover

theorem strip3_s019 {a z : ℝ} (ha1 : ((1/2 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7/10 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((3/5 : ℚ) : ℝ))) (h220 : a ≤ ((13/20 : ℚ) : ℝ)) (h221 : a ≤ ((5/8 : ℚ) : ℝ)) (h222 : z ≤ ((217/400 : ℚ) : ℝ)) (h223 : z ≤ ((1257/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h224 : z ≤ ((1601/8000 : ℚ) : ℝ)
  · -- left
    by_cases h225 : a ≤ ((49/80 : ℚ) : ℝ)
    · -- left
      by_cases h226 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        by_cases h227 : z ≤ ((733/6400 : ℚ) : ℝ)
        · -- left
          by_cases h228 : z ≤ ((6417/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B016.c326_pos (not_le.mp h0).le h225 hz1 h228
          · -- right
            exact CKLaneC2R.Cells.S03.B016.c328_pos (not_le.mp h0).le h225 (not_le.mp h228).le h227
        · -- right
          exact CKLaneC2R.Cells.S03.B011.c220_pos (not_le.mp h0).le h225 (not_le.mp h227).le h226
      · -- right
        by_cases h229 : z ≤ ((5491/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B011.c224_pos (not_le.mp h0).le h225 (not_le.mp h226).le h229
        · -- right
          exact CKLaneC2R.Cells.S03.B011.c226_pos (not_le.mp h0).le h225 (not_le.mp h229).le h224
    · -- right
      by_cases h230 : z ≤ ((2289/16000 : ℚ) : ℝ)
      · -- left
        by_cases h231 : z ≤ ((733/6400 : ℚ) : ℝ)
        · -- left
          by_cases h232 : z ≤ ((6417/64000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S03.B016.c327_pos (not_le.mp h225).le h221 hz1 h232
          · -- right
            exact CKLaneC2R.Cells.S03.B016.c329_pos (not_le.mp h225).le h221 (not_le.mp h232).le h231
        · -- right
          exact CKLaneC2R.Cells.S03.B011.c221_pos (not_le.mp h225).le h221 (not_le.mp h231).le h230
      · -- right
        by_cases h233 : z ≤ ((5491/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B011.c225_pos (not_le.mp h225).le h221 (not_le.mp h230).le h233
        · -- right
          exact CKLaneC2R.Cells.S03.B011.c227_pos (not_le.mp h225).le h221 (not_le.mp h233).le h224
  · -- right
    by_cases h234 : z ≤ ((823/3200 : ℚ) : ℝ)
    · -- left
      by_cases h235 : z ≤ ((7317/32000 : ℚ) : ℝ)
      · -- left
        by_cases h236 : a ≤ ((49/80 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S03.B012.c242_pos (not_le.mp h0).le h236 (not_le.mp h224).le h235
        · -- right
          exact CKLaneC2R.Cells.S03.B012.c243_pos (not_le.mp h236).le h221 (not_le.mp h224).le h235
      · -- right
        exact CKLaneC2R.Cells.S03.B001.c36_pos (not_le.mp h0).le h221 (not_le.mp h235).le h234
    · -- right
      by_cases h237 : z ≤ ((9143/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S03.B001.c39_pos (not_le.mp h0).le h221 (not_le.mp h234).le h237
      · -- right
        exact CKLaneC2R.Cells.S03.B002.c40_pos (not_le.mp h0).le h221 (not_le.mp h237).le h223

end CKLaneC2R.CompactCover


