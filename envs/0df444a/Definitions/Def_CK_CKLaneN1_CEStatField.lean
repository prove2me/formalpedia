-- Prove2me | Definitions.Def_CK_CKLaneN1_CEStatField
-- name    : CK_CKLaneN1_CEStatField
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T18:12:30.475167+00:00
-- url     : https://prove2.me/theorems/fa4a26c6-4e2d-45dc-b4ea-7c8a11f0f1a0
-- title:
--   Courtade–Kumar proof module `CKLaneN1.CEStatField` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.CEStatField` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.CEStatField` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.CEStatField (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/CEStatField.lean)

import Definitions.Def_CK_CKLaneN1_CEStatCapital

-- ===== source module CKLaneN1.CEStatField =====
section

set_option autoImplicit false

/-!
# Lane N1: `leftStationary` from the three CE-stat rows still open elsewhere (CONDITIONAL)

Rows 1 (`retainedDomainExclusion`) and 2 (`capitalExclusion`) are closed in lane N1. Rows 3
(`TransverseCurvatureOwner`) and 4 (`A3LeafUnion`) belong to lane M07, row 5 (`HighTCExclusion`) to
lane A1. This adapter is CONDITIONAL on those three rows; it closes nothing by itself.
-/

namespace CKLaneN1.CEStat

open GeneralCK GeneralCK.SmallMeanPhiCutoff

/-- CONDITIONAL (not a closure): the field `leftStationary` (at `S = retainedCutoff`) from CE-stat
rows 3, 4, 5. -/
theorem leftStationary_of_rows345 (h3 : TransverseCurvatureOwner) (h4 : A3LeafUnion)
    (h5 : HighTCExclusion) : LeftStationaryField :=
  leftStationary_of_owners ⟨retainedDomainExclusion, Capital.capitalExclusion, h3, h4, h5⟩

end CKLaneN1.CEStat

end


