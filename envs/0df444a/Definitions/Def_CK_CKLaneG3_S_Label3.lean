-- Prove2me | Definitions.Def_CK_CKLaneG3_S_Label3
-- name    : CK_CKLaneG3_S_Label3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T00:24:13.113976+00:00
-- url     : https://prove2.me/theorems/6fae7a25-e81f-46b3-8135-1a9b7d13c034
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.Label3` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.Label3` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.Label3` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.Label3 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/Label3.lean)

import Definitions.Def_CK_CKLaneG3_S_Label3_q101

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.Label3
open CKLaneD CKLaneG3 CKLaneG3.S
/-- Every archived (S) leaf with owner label 3 satisfies the `SS_Compact` obligation. -/
theorem label3 : ∀ q ∈ sTree.leaves, q.2 = 3 → SLeafOK (sBox q.1) :=
  sLabel_family_of_slices 3 SH Prod.fst SH_ok runs (by decide +kernel)

end CKLaneG3.S.Label3


