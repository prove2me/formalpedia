-- Prove2me | Definitions.Def_CK_CKLaneA5_Correction_q00
-- name    : CK_CKLaneA5_Correction_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-09T15:30:53.778975+00:00
-- url     : https://prove2.me/theorems/b6f7a68c-0476-4a83-a0d0-46bd7893292b
-- title:
--   Courtade–Kumar proof module `CKLaneA5.Correction (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA5.Correction (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA5.Correction (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA5.Correction (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA5/Correction (piece 1 of 3).lean)

import Definitions.Def_CK_CKLaneA5_ChartOwnersAsm
import Definitions.Def_CK_CKLaneA5_Bands


/-!
# Lane A5: `correctionLeft` / `correctionDet` at the exact `CKRoute.Theorem71Components` field types

`GeneralCK.Correction.Complement.orderedTriangle_signs_of_charts` applied to
* `CKLaneA5.Bands.band1_actual : ActualRatioFamilyOn (1/50) (1/10) (3/40) 1` (R-B1 cover),
* `CKLaneA5.Bands.band2_actual : ActualRatioFamilyOn (1/10) (1/5) (1/10) 1` (R-B2 owner),
* `CKLaneA5.Assembly.chartOwners : ChartOwners` (lanes A1, A2, A3, A4, A5).

Provider: private merged root `A/asmroot5` (F-C root + R-B1/R-B2 band modules, manifest A/a5/asmroot5_manifest.tsv).
-/

namespace CKLaneA5.Assembly

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Complement

theorem correction_signs :
    (∀ p ∈ orderedTriangle, 0 < Mleft p.1 p.2) ∧ (∀ p ∈ orderedTriangle, 0 ≤ Mdet p.1 p.2) :=
  orderedTriangle_signs_of_charts CKLaneA5.Bands.band1_actual CKLaneA5.Bands.band2_actual chartOwners

end CKLaneA5.Assembly


