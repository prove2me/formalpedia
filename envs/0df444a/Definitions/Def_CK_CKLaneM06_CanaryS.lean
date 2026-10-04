-- Prove2me | Definitions.Def_CK_CKLaneM06_CanaryS
-- name    : CK_CKLaneM06_CanaryS
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T12:21:54.981589+00:00
-- url     : https://prove2.me/theorems/4d761205-c8fb-4157-a8c3-05c9e2c061d4
-- title:
--   Courtade–Kumar proof module `CKLaneM06.CanaryS` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM06.CanaryS` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM06.CanaryS` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM06.CanaryS (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM06/CanaryS.lean)

import Definitions.Def_CK_CKLaneM06_Canary
import Definitions.Def_CK_CKLaneM06_SForm

-- ===== source module CKLaneM06.CanaryS =====
section

/-!
# Lane M06 canary in the BRIEF §7 same-side form

The hardest archived `parent_tail` leaf `4444444444444444513`, restated over `InS (sBox path)`
(exact `COVER.reconstruct` box, BRIEF §7 membership).
-/

set_option autoImplicit false

namespace CKLaneM06.Canary

open CKLaneM06

/-- The exact archived box in BRIEF §7 fields. -/
theorem sBox_eq : sBox path = ⟨16, 32, 17 / 64, 1 / 2, 1 / 131072, 1 / 65536⟩ := by
  decide +kernel

/-- **Canary (BRIEF §7 form).** Parent dominance on `InS (sBox path)`. -/
theorem canary_parentS : ParentS (sBox path) := canary_dominance.toParentS

/-- **Canary (BRIEF §7 form, strict psi-activity owner).** -/
theorem canary_ownerS : OwnerS (sBox path) := canary_parentS.ownerS

end CKLaneM06.Canary

end


