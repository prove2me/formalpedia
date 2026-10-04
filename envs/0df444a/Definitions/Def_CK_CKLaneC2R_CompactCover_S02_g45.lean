-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g45
-- name    : CK_CKLaneC2R_CompactCover_S02_g45
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T07:10:14.265605+00:00
-- url     : https://prove2.me/theorems/48d85f39-d752-4d21-9e0c-4021d38e63ca
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B012
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B014
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B027
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B028
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B036
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B037
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B040
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B041

namespace CKLaneC2R.CompactCover

theorem strip2_s067 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : a ≤ ((9/20 : ℚ) : ℝ)) (h535 : ¬ (a ≤ ((17/40 : ℚ) : ℝ))) (h630 : ¬ (a ≤ ((7/16 : ℚ) : ℝ))) (h675 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h696 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h703 : z ≤ ((7079/8000 : ℚ) : ℝ)
  · -- left
    by_cases h704 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h705 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B012.c251_pos (not_le.mp h630).le h534 (not_le.mp h696).le h705
      · -- right
        exact CKLaneC2R.Cells.S02.B012.c252_pos (not_le.mp h630).le h534 (not_le.mp h705).le h704
    · -- right
      by_cases h706 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B012.c258_pos (not_le.mp h630).le h534 (not_le.mp h704).le h706
      · -- right
        exact CKLaneC2R.Cells.S02.B013.c260_pos (not_le.mp h630).le h534 (not_le.mp h706).le h703
  · -- right
    by_cases h707 : z ≤ ((15071/16000 : ℚ) : ℝ)
    · -- left
      by_cases h708 : z ≤ ((29229/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B014.c281_pos (not_le.mp h630).le h534 (not_le.mp h703).le h708
      · -- right
        by_cases h709 : z ≤ ((59371/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B027.c553_pos (not_le.mp h630).le h534 (not_le.mp h708).le h709
        · -- right
          exact CKLaneC2R.Cells.S02.B027.c554_pos (not_le.mp h630).le h534 (not_le.mp h709).le h707
    · -- right
      by_cases h710 : z ≤ ((6211/6400 : ℚ) : ℝ)
      · -- left
        by_cases h711 : z ≤ ((61197/64000 : ℚ) : ℝ)
        · -- left
          exact CKLaneC2R.Cells.S02.B028.c568_pos (not_le.mp h630).le h534 (not_le.mp h707).le h711
        · -- right
          exact CKLaneC2R.Cells.S02.B028.c570_pos (not_le.mp h630).le h534 (not_le.mp h711).le h710
      · -- right
        by_cases h712 : z ≤ ((63023/64000 : ℚ) : ℝ)
        · -- left
          by_cases h713 : z ≤ ((125133/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B036.c736_pos (not_le.mp h630).le h534 (not_le.mp h710).le h713
          · -- right
            exact CKLaneC2R.Cells.S02.B036.c738_pos (not_le.mp h630).le h534 (not_le.mp h713).le h712
        · -- right
          by_cases h714 : z ≤ ((126959/128000 : ℚ) : ℝ)
          · -- left
            exact CKLaneC2R.Cells.S02.B037.c750_pos (not_le.mp h630).le h534 (not_le.mp h712).le h714
          · -- right
            by_cases h715 : z ≤ ((254831/256000 : ℚ) : ℝ)
            · -- left
              exact CKLaneC2R.Cells.S02.B040.c808_pos (not_le.mp h630).le h534 (not_le.mp h714).le h715
            · -- right
              by_cases h716 : z ≤ ((20423/20480 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S02.B041.c829_pos (not_le.mp h630).le h534 (not_le.mp h715).le h716
              · -- right
                exact CKLaneC2R.Cells.S02.B041.c831_pos (not_le.mp h630).le h534 (not_le.mp h716).le hz2

end CKLaneC2R.CompactCover


