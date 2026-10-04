-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g12
-- name    : CK_CKLaneC2R_CompactCover_S02_g12
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T16:42:10.20699+00:00
-- url     : https://prove2.me/theorems/30bf151c-e653-48a7-8877-59e6595ae28d
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B017
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B018
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B001
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B007
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B025

namespace CKLaneC2R.CompactCover

theorem strip2_s018 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((13/40 : ℚ) : ℝ))) (h179 : a ≤ ((27/80 : ℚ) : ℝ)) (h180 : z ≤ ((217/400 : ℚ) : ℝ)) (h181 : ¬ (z ≤ ((1257/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h207 : z ≤ ((3427/8000 : ℚ) : ℝ)
  · -- left
    by_cases h208 : a ≤ ((53/160 : ℚ) : ℝ)
    · -- left
      by_cases h209 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        by_cases h210 : z ≤ ((10969/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B017.c352_pos (not_le.mp h2).le h208 (not_le.mp h181).le h210
        · -- right
          exact CKLaneC2R.Cells.S02.B017.c354_pos (not_le.mp h2).le h208 (not_le.mp h210).le h209
      · -- right
        by_cases h211 : z ≤ ((2559/6400 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B018.c360_pos (not_le.mp h2).le h208 (not_le.mp h209).le h211
        · -- right
          exact CKLaneC2R.Cells.S02.B018.c362_pos (not_le.mp h2).le h208 (not_le.mp h211).le h207
    · -- right
      by_cases h212 : z ≤ ((5941/16000 : ℚ) : ℝ)
      · -- left
        by_cases h213 : z ≤ ((10969/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B017.c353_pos (not_le.mp h208).le h179 (not_le.mp h181).le h213
        · -- right
          exact CKLaneC2R.Cells.S02.B017.c355_pos (not_le.mp h208).le h179 (not_le.mp h213).le h212
      · -- right
        by_cases h214 : z ≤ ((2559/6400 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B018.c361_pos (not_le.mp h208).le h179 (not_le.mp h212).le h214
        · -- right
          exact CKLaneC2R.Cells.S02.B018.c363_pos (not_le.mp h208).le h179 (not_le.mp h214).le h207
  · -- right
    by_cases h215 : z ≤ ((7767/16000 : ℚ) : ℝ)
    · -- left
      by_cases h216 : a ≤ ((53/160 : ℚ) : ℝ)
      · -- left
        by_cases h217 : z ≤ ((14621/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B018.c366_pos (not_le.mp h2).le h216 (not_le.mp h207).le h217
        · -- right
          exact CKLaneC2R.Cells.S02.B018.c368_pos (not_le.mp h2).le h216 (not_le.mp h217).le h215
      · -- right
        by_cases h218 : z ≤ ((14621/32000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B018.c367_pos (not_le.mp h216).le h179 (not_le.mp h207).le h218
        · -- right
          exact CKLaneC2R.Cells.S02.B018.c369_pos (not_le.mp h216).le h179 (not_le.mp h218).le h215
    · -- right
      by_cases h219 : z ≤ ((16447/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B001.c27_pos (not_le.mp h2).le h179 (not_le.mp h215).le h219
      · -- right
        exact CKLaneC2R.Cells.S02.B001.c28_pos (not_le.mp h2).le h179 (not_le.mp h219).le h180

theorem strip2_s019 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((13/40 : ℚ) : ℝ))) (h179 : a ≤ ((27/80 : ℚ) : ℝ)) (h180 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h220 : z ≤ ((3083/4000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h221 : z ≤ ((5253/8000 : ℚ) : ℝ)
  · -- left
    by_cases h222 : z ≤ ((9593/16000 : ℚ) : ℝ)
    · -- left
      by_cases h223 : z ≤ ((18273/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B007.c146_pos (not_le.mp h2).le h179 (not_le.mp h180).le h223
      · -- right
        exact CKLaneC2R.Cells.S02.B007.c147_pos (not_le.mp h2).le h179 (not_le.mp h223).le h222
    · -- right
      by_cases h224 : z ≤ ((20099/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B007.c150_pos (not_le.mp h2).le h179 (not_le.mp h222).le h224
      · -- right
        exact CKLaneC2R.Cells.S02.B007.c151_pos (not_le.mp h2).le h179 (not_le.mp h224).le h221
  · -- right
    by_cases h225 : z ≤ ((11419/16000 : ℚ) : ℝ)
    · -- left
      by_cases h226 : z ≤ ((877/1280 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B007.c154_pos (not_le.mp h2).le h179 (not_le.mp h221).le h226
      · -- right
        exact CKLaneC2R.Cells.S02.B007.c155_pos (not_le.mp h2).le h179 (not_le.mp h226).le h225
    · -- right
      by_cases h227 : z ≤ ((23751/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B007.c158_pos (not_le.mp h2).le h179 (not_le.mp h225).le h227
      · -- right
        exact CKLaneC2R.Cells.S02.B007.c159_pos (not_le.mp h2).le h179 (not_le.mp h227).le h220

theorem strip2_s020 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : a ≤ ((2/5 : ℚ) : ℝ)) (h1 : a ≤ ((7/20 : ℚ) : ℝ)) (h2 : ¬ (a ≤ ((13/40 : ℚ) : ℝ))) (h179 : a ≤ ((27/80 : ℚ) : ℝ)) (h180 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h220 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h228 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h229 : a ≤ ((53/160 : ℚ) : ℝ)
  · -- left
    by_cases h230 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h231 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B025.c505_pos (not_le.mp h2).le h229 (not_le.mp h220).le h231
      · -- right
        exact CKLaneC2R.Cells.S02.B025.c507_pos (not_le.mp h2).le h229 (not_le.mp h231).le h230
    · -- right
      by_cases h232 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B025.c509_pos (not_le.mp h2).le h229 (not_le.mp h230).le h232
      · -- right
        exact CKLaneC2R.Cells.S02.B025.c511_pos (not_le.mp h2).le h229 (not_le.mp h232).le h228
  · -- right
    by_cases h233 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h234 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B025.c506_pos (not_le.mp h229).le h179 (not_le.mp h220).le h234
      · -- right
        exact CKLaneC2R.Cells.S02.B025.c508_pos (not_le.mp h229).le h179 (not_le.mp h234).le h233
    · -- right
      by_cases h235 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B025.c510_pos (not_le.mp h229).le h179 (not_le.mp h233).le h235
      · -- right
        exact CKLaneC2R.Cells.S02.B025.c512_pos (not_le.mp h229).le h179 (not_le.mp h235).le h228

end CKLaneC2R.CompactCover


