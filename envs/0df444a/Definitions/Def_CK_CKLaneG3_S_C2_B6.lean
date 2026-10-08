-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C2_B6
-- name    : CK_CKLaneG3_S_C2_B6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T16:35:42.515951+00:00
-- url     : https://prove2.me/theorems/6bd9abfd-f95f-4ab7-8d31-6af69c6b513b
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C2.B6` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C2.B6` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C2.B6` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C2.B6 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C2/B6.lean)

import Definitions.Def_CK_CKLaneG3_S_C2_B6_q02

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C2.B6
open CKLaneD CKLaneG3
def r_5030010421_0 : List (ℕ × ℕ × ℕ) := [(32, 0, 140), (33, 0, 120), (34, 0, 68), (35, 0, 118), (36, 0, 117), (37, 0, 111), (38, 0, 79), (39, 0, 108)]
/-- chunk `5030010421`: 861 label-2 leaves. -/
theorem c_5030010421 : ∀ q ∈ CKLaneG3.S.Chunk.C_5030010421.t.leavesR [1, 2, 4, 0, 1, 0, 0, 3, 0, 5], q.2 = 2 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_5030010421.t 2 [1, 2, 4, 0, 1, 0, 0, 3, 0, 5] SH id SH_ok
    (r_5030010421_0) (by decide +kernel)

end CKLaneG3.S.C2.B6


