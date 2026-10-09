-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B18
-- name    : CK_CKLaneG3_S_C0_B18
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-09T03:03:27.444119+00:00
-- url     : https://prove2.me/theorems/c5616211-e654-45b8-a864-82b926ed9b83
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B18` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B18` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B18` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B18 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B18.lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B18_q02

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B18
open CKLaneD CKLaneG3
/-- chunk `50300115`: 122 label-0 leaves. -/
theorem c_50300115 : ∀ q ∈ CKLaneG3.S.Chunk.C_50300115.t.leavesR [5, 1, 1, 0, 0, 3, 0, 5], q.2 = 0 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_50300115.t 0 [5, 1, 1, 0, 0, 3, 0, 5] SH id SH_ok
    (r_50300115_0) (by decide +kernel)

end CKLaneG3.S.C0.B18


