-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B18_q01
-- name    : CK_CKLaneG3_S_C0_B18_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T13:07:49.007423+00:00
-- url     : https://prove2.me/theorems/d1a1d6ff-4764-4793-8910-c5a6ded36f28
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B18 (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B18 (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B18 (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B18 (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B18 (piece 2 of 3).lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B18_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B18
open CKLaneD CKLaneG3
/-- chunk `5030010531431`: 0 label-0 leaves. -/
theorem c_5030010531431 : ∀ q ∈ CKLaneG3.S.Chunk.C_5030010531431.t.leavesR [1, 3, 4, 1, 3, 5, 0, 1, 0, 0, 3, 0, 5], q.2 = 0 → SLeafOK (sBox q.1) :=
  sub_family_of_none (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_5030010531431.t 0 [1, 3, 4, 1, 3, 5, 0, 1, 0, 0, 3, 0, 5] (by decide +kernel)

def r_50300105315_0 : List (ℕ × ℕ × ℕ) := [(6, 20, 19)]
/-- chunk `50300105315`: 19 label-0 leaves. -/
theorem c_50300105315 : ∀ q ∈ CKLaneG3.S.Chunk.C_50300105315.t.leavesR [5, 1, 3, 5, 0, 1, 0, 0, 3, 0, 5], q.2 = 0 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_50300105315.t 0 [5, 1, 3, 5, 0, 1, 0, 0, 3, 0, 5] SH id SH_ok
    (r_50300105315_0) (by decide +kernel)

def r_503001142_0 : List (ℕ × ℕ × ℕ) := [(0, 44, 9), (0, 54, 1), (0, 53, 1), (0, 55, 2), (0, 58, 6), (0, 65, 3), (1, 50, 3)]
end CKLaneG3.S.C0.B18


