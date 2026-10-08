-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C2_B0
-- name    : CK_CKLaneG3_S_C2_B0
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T04:31:22.600926+00:00
-- url     : https://prove2.me/theorems/409d62ae-c240-4090-bcb6-79f48497fd65
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C2.B0` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C2.B0` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C2.B0` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C2.B0 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C2/B0.lean)

import Definitions.Def_CK_CKLaneG3_S_C2_B0_q01

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C2.B0
open CKLaneD CKLaneG3
/-- chunk `502020203040`: 161 label-2 leaves. -/
theorem c_502020203040 : ∀ q ∈ CKLaneG3.S.Chunk.C_502020203040.t.leavesR [0, 4, 0, 3, 0, 2, 0, 2, 0, 2, 0, 5], q.2 = 2 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_502020203040.t 2 [0, 4, 0, 3, 0, 2, 0, 2, 0, 2, 0, 5] SH id SH_ok
    (r_502020203040_0) (by decide +kernel)

def r_5020202030414_0 : List (ℕ × ℕ × ℕ) := [(23, 89, 28), (24, 0, 112), (25, 0, 110), (26, 0, 95), (27, 0, 52)]
/-- chunk `5020202030414`: 397 label-2 leaves. -/
theorem c_5020202030414 : ∀ q ∈ CKLaneG3.S.Chunk.C_5020202030414.t.leavesR [4, 1, 4, 0, 3, 0, 2, 0, 2, 0, 2, 0, 5], q.2 = 2 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_5020202030414.t 2 [4, 1, 4, 0, 3, 0, 2, 0, 2, 0, 2, 0, 5] SH id SH_ok
    (r_5020202030414_0) (by decide +kernel)

def r_5020202030415_0 : List (ℕ × ℕ × ℕ) := [(27, 52, 68), (28, 0, 2)]
/-- chunk `5020202030415`: 70 label-2 leaves. -/
theorem c_5020202030415 : ∀ q ∈ CKLaneG3.S.Chunk.C_5020202030415.t.leavesR [5, 1, 4, 0, 3, 0, 2, 0, 2, 0, 2, 0, 5], q.2 = 2 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_5020202030415.t 2 [5, 1, 4, 0, 3, 0, 2, 0, 2, 0, 2, 0, 5] SH id SH_ok
    (r_5020202030415_0) (by decide +kernel)

end CKLaneG3.S.C2.B0


