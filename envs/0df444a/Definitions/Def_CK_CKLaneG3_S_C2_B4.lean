-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C2_B4
-- name    : CK_CKLaneG3_S_C2_B4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T20:57:49.863213+00:00
-- url     : https://prove2.me/theorems/c9fbcfa2-4143-48f7-9fab-0267853592e5
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C2.B4` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C2.B4` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C2.B4` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C2.B4 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C2/B4.lean)

import Definitions.Def_CK_CKLaneG3_S_C2_B4_q01

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C2.B4
open CKLaneD CKLaneG3
/-- chunk `5021`: 0 label-2 leaves. -/
theorem c_5021 : ∀ q ∈ CKLaneG3.S.Chunk.C_5021.t.leavesR [1, 2, 0, 5], q.2 = 2 → SLeafOK (sBox q.1) :=
  sub_family_of_none (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_5021.t 2 [1, 2, 0, 5] (by decide +kernel)

/-- chunk `5030000`: 0 label-2 leaves. -/
theorem c_5030000 : ∀ q ∈ CKLaneG3.S.Chunk.C_5030000.t.leavesR [0, 0, 0, 0, 3, 0, 5], q.2 = 2 → SLeafOK (sBox q.1) :=
  sub_family_of_none (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_5030000.t 2 [0, 0, 0, 0, 3, 0, 5] (by decide +kernel)

def r_50300014_0 : List (ℕ × ℕ × ℕ) := [(28, 34, 76), (29, 0, 195), (30, 0, 119), (31, 0, 113), (32, 0, 120), (33, 0, 111), (34, 0, 72), (35, 0, 176), (36, 0, 106), (37, 0, 41)]
/-- chunk `50300014`: 1129 label-2 leaves. -/
theorem c_50300014 : ∀ q ∈ CKLaneG3.S.Chunk.C_50300014.t.leavesR [4, 1, 0, 0, 0, 3, 0, 5], q.2 = 2 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_50300014.t 2 [4, 1, 0, 0, 0, 3, 0, 5] SH id SH_ok
    (r_50300014_0) (by decide +kernel)

def r_5030001520_0 : List (ℕ × ℕ × ℕ) := [(37, 41, 79), (38, 0, 74)]
/-- chunk `5030001520`: 153 label-2 leaves. -/
theorem c_5030001520 : ∀ q ∈ CKLaneG3.S.Chunk.C_5030001520.t.leavesR [0, 2, 5, 1, 0, 0, 0, 3, 0, 5], q.2 = 2 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_5030001520.t 2 [0, 2, 5, 1, 0, 0, 0, 3, 0, 5] SH id SH_ok
    (r_5030001520_0) (by decide +kernel)

end CKLaneG3.S.C2.B4


