-- Prove2me | Definitions.Def_CK_CKLaneA5_Bands
-- name    : CK_CKLaneA5_Bands
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T17:40:51.732154+00:00
-- url     : https://prove2.me/theorems/c8074b58-daac-48cc-8ccb-81525f1d3e5c
-- title:
--   Courtade–Kumar proof module `CKLaneA5.Bands` (transplant, CKFast certificate inputs)
-- statement:
--   Transplant of the Lean module `CKLaneA5.Bands` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), with one substantive change: the certificate inputs it consumes are replaced by the platform theorems `GeneralCK.CKFast.hC1_actual`, `GeneralCK.CKFast.hC2_actual` (correction bands R-B1, R-B2) and `GeneralCK.CKFast.directC3_actual` (chart owner `directC3`). These are proved on this platform by the computing interval checker `GeneralCK.CKFast.tree_sound` instead of the source's stored certificates, and they state exactly the source's `ActualRatioFamilyOn` inputs in unfolded form. Everything else is the original source, with project imports redirected to their transplanted bundles `Definitions.Def_CK_*`.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA5.Bands` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA5.Bands (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA5/Bands.lean)

import Definitions.Def_CK_GeneralCK_CorrectionComplementCharts
import Theorems.Thm_GeneralCK_CKFast_hC1_actual
import Theorems.Thm_GeneralCK_CKFast_hC2_actual

/-!
# Lane A5: the two certified bands, in the form consumed by `orderedTriangle_signs_of_charts`

Transplant of `CKLaneA5.Bands`. In the source, `band1_actual` / `band2_actual` come from the
R-B1 / R-B2 certificate covers (17,675 cells). On this platform the same two propositions are the
proved theorems `GeneralCK.CKFast.hC1_actual` / `GeneralCK.CKFast.hC2_actual` (computing checker),
which state `ActualRatioFamilyOn` unfolded.
-/

namespace CKLaneA5.Bands

open GeneralCK GeneralCK.Correction

theorem band1_actual : ActualRatioFamilyOn (1 / 50) (1 / 10) (3 / 40) 1 :=
  fun _ _ hu hr hr1 => GeneralCK.CKFast.hC1_actual hu hr hr1

theorem band2_actual : ActualRatioFamilyOn (1 / 10) (1 / 5) (1 / 10) 1 :=
  fun _ _ hu hr hr1 => GeneralCK.CKFast.hC2_actual hu hr hr1

end CKLaneA5.Bands


