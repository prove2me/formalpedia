-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S05_g16
-- name    : CK_CKLaneC2R_CompactCover_S05_g16
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T13:34:30.178118+00:00
-- url     : https://prove2.me/theorems/c418e48f-a0af-4c41-8ceb-159223edf4bb
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

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S05_B018

namespace CKLaneC2R.CompactCover

theorem strip5_s026 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : a ≤ ((3897/4000 : ℚ) : ℝ)) (h148 : ¬ (a ≤ ((1539/1600 : ℚ) : ℝ))) (h199 : a ≤ ((15489/16000 : ℚ) : ℝ)) (h200 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h208 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h212 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h216 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h217 : z ≤ ((29229/32000 : ℚ) : ℝ)
  · -- left
    by_cases h218 : z ≤ ((11509/12800 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B013.c273_pos (not_le.mp h148).le h199 (not_le.mp h212).le h218
    · -- right
      exact CKLaneC2R.Cells.S05.B013.c274_pos (not_le.mp h148).le h199 (not_le.mp h218).le h217
  · -- right
    by_cases h219 : z ≤ ((59371/64000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B014.c281_pos (not_le.mp h148).le h199 (not_le.mp h217).le h219
    · -- right
      exact CKLaneC2R.Cells.S05.B014.c282_pos (not_le.mp h148).le h199 (not_le.mp h219).le h216

theorem strip5_s027 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((1899/2000 : ℚ) : ℝ))) (h147 : a ≤ ((3897/4000 : ℚ) : ℝ)) (h148 : ¬ (a ≤ ((1539/1600 : ℚ) : ℝ))) (h199 : a ≤ ((15489/16000 : ℚ) : ℝ)) (h200 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h208 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h212 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h216 : ¬ (z ≤ ((15071/16000 : ℚ) : ℝ))) (h220 : z ≤ ((6211/6400 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h221 : z ≤ ((61197/64000 : ℚ) : ℝ)
  · -- left
    by_cases h222 : a ≤ ((30879/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B018.c361_pos (not_le.mp h148).le h222 (not_le.mp h216).le h221
    · -- right
      exact CKLaneC2R.Cells.S05.B018.c362_pos (not_le.mp h222).le h199 (not_le.mp h216).le h221
  · -- right
    by_cases h223 : z ≤ ((123307/128000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S05.B018.c365_pos (not_le.mp h148).le h199 (not_le.mp h221).le h223
    · -- right
      exact CKLaneC2R.Cells.S05.B018.c366_pos (not_le.mp h148).le h199 (not_le.mp h223).le h220

end CKLaneC2R.CompactCover


