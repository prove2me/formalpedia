-- Prove2me | Definitions.Def_CK_CKLaneC2R_CompactCover_S02_g53
-- name    : CK_CKLaneC2R_CompactCover_S02_g53
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T20:05:06.391014+00:00
-- url     : https://prove2.me/theorems/c96e2a8a-e5f2-4ce7-a15f-f7f75189b1b8
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

import Definitions.Def_CK_CKLaneC2R_Cells_S02_B013
import Definitions.Def_CK_CKLaneC2R_Cells_S02_B014

namespace CKLaneC2R.CompactCover

theorem strip2_s079 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : ¬ (a ≤ ((9/20 : ℚ) : ℝ))) (h717 : ¬ (a ≤ ((19/40 : ℚ) : ℝ))) (h792 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h823 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h831 : z ≤ ((7079/8000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h832 : a ≤ ((39/80 : ℚ) : ℝ)
  · -- left
    by_cases h833 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h834 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B013.c265_pos (not_le.mp h717).le h832 (not_le.mp h823).le h834
      · -- right
        exact CKLaneC2R.Cells.S02.B013.c266_pos (not_le.mp h717).le h832 (not_le.mp h834).le h833
    · -- right
      by_cases h835 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B013.c273_pos (not_le.mp h717).le h832 (not_le.mp h833).le h835
      · -- right
        exact CKLaneC2R.Cells.S02.B013.c275_pos (not_le.mp h717).le h832 (not_le.mp h835).le h831
  · -- right
    by_cases h836 : z ≤ ((2649/3200 : ℚ) : ℝ)
    · -- left
      by_cases h837 : z ≤ ((25577/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B013.c267_pos (not_le.mp h832).le ha2 (not_le.mp h823).le h837
      · -- right
        exact CKLaneC2R.Cells.S02.B013.c268_pos (not_le.mp h832).le ha2 (not_le.mp h837).le h836
    · -- right
      by_cases h838 : z ≤ ((27403/32000 : ℚ) : ℝ)
      · -- left
        exact CKLaneC2R.Cells.S02.B013.c274_pos (not_le.mp h832).le ha2 (not_le.mp h836).le h838
      · -- right
        exact CKLaneC2R.Cells.S02.B013.c276_pos (not_le.mp h832).le ha2 (not_le.mp h838).le h831

theorem strip2_s080 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) (h0 : ¬ (a ≤ ((2/5 : ℚ) : ℝ))) (h534 : ¬ (a ≤ ((9/20 : ℚ) : ℝ))) (h717 : ¬ (a ≤ ((19/40 : ℚ) : ℝ))) (h792 : ¬ (z ≤ ((217/400 : ℚ) : ℝ))) (h823 : ¬ (z ≤ ((3083/4000 : ℚ) : ℝ))) (h831 : ¬ (z ≤ ((7079/8000 : ℚ) : ℝ))) (h839 : z ≤ ((15071/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h840 : a ≤ ((39/80 : ℚ) : ℝ)
  · -- left
    by_cases h841 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B014.c286_pos (not_le.mp h717).le h840 (not_le.mp h831).le h841
    · -- right
      exact CKLaneC2R.Cells.S02.B014.c288_pos (not_le.mp h717).le h840 (not_le.mp h841).le h839
  · -- right
    by_cases h842 : z ≤ ((29229/32000 : ℚ) : ℝ)
    · -- left
      exact CKLaneC2R.Cells.S02.B014.c287_pos (not_le.mp h840).le ha2 (not_le.mp h831).le h842
    · -- right
      exact CKLaneC2R.Cells.S02.B014.c289_pos (not_le.mp h840).le ha2 (not_le.mp h842).le h839

end CKLaneC2R.CompactCover


