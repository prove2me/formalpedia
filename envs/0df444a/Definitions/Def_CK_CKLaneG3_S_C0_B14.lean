-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B14
-- name    : CK_CKLaneG3_S_C0_B14
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-10T11:00:17.337193+00:00
-- url     : https://prove2.me/theorems/d8696ce2-19fe-4ae3-9d3e-57bbb6945795
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B14` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B14` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B14` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B14 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B14.lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B14_q02

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B14
open CKLaneD CKLaneG3
def r_503000153_0 : List (ℕ × ℕ × ℕ) := [(52, 58, 6), (52, 24, 1), (52, 64, 6), (52, 28, 1), (52, 70, 4), (52, 31, 1), (53, 0, 9), (52, 19, 5), (52, 25, 3), (52, 29, 2), (52, 32, 24), (52, 57, 1), (52, 56, 1)]
/-- chunk `503000153`: 64 label-0 leaves. -/
theorem c_503000153 : ∀ q ∈ CKLaneG3.S.Chunk.C_503000153.t.leavesR [3, 5, 1, 0, 0, 0, 3, 0, 5], q.2 = 0 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_503000153.t 0 [3, 5, 1, 0, 0, 0, 3, 0, 5] SH id SH_ok
    (r_503000153_0) (by decide +kernel)

end CKLaneG3.S.C0.B14


