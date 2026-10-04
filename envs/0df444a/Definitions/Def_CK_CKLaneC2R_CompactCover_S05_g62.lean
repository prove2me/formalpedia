-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g62
-- name    : CK_CKLaneC2R_CompactCover_S05_g62
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T10:41:13.298182+00:00
-- url     : https://prove2.me/theorems/e613ebad-18ed-42fd-9811-d92bff5f2510
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B029
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B030
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B031

namespace CKLaneC2R.CompactCover

theorem strip5_s121 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : ¬ (a ≤ ((127773/128000 : ℚ) : ℝ))) (h667 : ¬ (a ≤ ((51129/51200 : ℚ) : ℝ))) (h694 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h703 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h706 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h708 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h710 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h711 : z ≤ ((61197/64000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B027.c543_pos (not_le.mp h667).le ha2 (not_le.mp h708).le h711
  · -- right
    by_cases h712 : a ≤ ((511389/512000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B029.c583_pos (not_le.mp h667).le h712 (not_le.mp h711).le h710
    · -- right
      exact CKLaneC2R.Cells.S05.B029.c584_pos (not_le.mp h712).le ha2 (not_le.mp h711).le h710

theorem strip5_s122 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : ¬ (a ≤ ((3897/4000 : ℚ) : ℝ))) (h271 : ¬ (a ≤ ((7893/8000 : ℚ) : ℝ))) (h376 : ¬ (a ≤ ((3177/3200 : ℚ) : ℝ))) (h473 : ¬ (a ≤ ((31869/32000 : ℚ) : ℝ))) (h550 : ¬ (a ≤ ((63837/64000 : ℚ) : ℝ))) (h616 : ¬ (a ≤ ((127773/128000 : ℚ) : ℝ))) (h667 : ¬ (a ≤ ((51129/51200 : ℚ) : ℝ))) (h694 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h703 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h706 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h708 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h710 : ¬ (z ≤ ((6211/6400 : ℚ) : ℝ))) (h713 : z ≤ ((63023/64000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h714 : z ≤ ((125133/128000 : ℚ) : ℝ)
  · -- left
    exact CKLaneC2R.Cells.S05.B030.c602_pos (not_le.mp h667).le ha2 (not_le.mp h710).le h714
  · -- right
    by_cases h715 : a ≤ ((511389/512000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B031.c626_pos (not_le.mp h667).le h715 (not_le.mp h714).le h713
    · -- right
      exact CKLaneC2R.Cells.S05.B031.c627_pos (not_le.mp h715).le ha2 (not_le.mp h714).le h713

end CKLaneC2R.CompactCover


