-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B11_q01_q02
-- name    : CK_CKLaneG3_S_C0_B11_q01_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T02:07:43.220055+00:00
-- url     : https://prove2.me/theorems/3b5e13bd-8c2c-4eac-8070-e94d3598eb2b
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B11 (piece 2 of 3) (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B11 (piece 2 of 3) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B11 (piece 2 of 3) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B11 (piece 2 of 3) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B11 (piece 2 of 3) (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B11_q01_q01

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B11
open CKLaneD CKLaneG3
/-- chunk `50203001431`: 1575 label-0 leaves. -/
theorem c_50203001431 : ∀ q ∈ CKLaneG3.S.Chunk.C_50203001431.t.leavesR [1, 3, 4, 1, 0, 0, 3, 0, 2, 0, 5], q.2 = 0 → SLeafOK (sBox q.1) :=
  sub_family_of_slices (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_50203001431.t 0 [1, 3, 4, 1, 0, 0, 3, 0, 2, 0, 5] SH id SH_ok
    (r_50203001431_0 ++ (r_50203001431_1 ++ (r_50203001431_2 ++ (r_50203001431_3 ++ (r_50203001431_4 ++ (r_50203001431_5 ++ (r_50203001431_6 ++ (r_50203001431_7 ++ (r_50203001431_8))))))))) (by decide +kernel)

def r_5020300152_0 : List (ℕ × ℕ × ℕ) := [(0, 168, 10), (1, 66, 1), (0, 178, 2), (6, 232, 1), (1, 67, 2), (6, 233, 2), (1, 69, 2), (6, 235, 2), (0, 217, 1), (0, 237, 1), (6, 249, 3), (0, 258, 1), (1, 18, 1), (0, 259, 1), (1, 19, 1), (6, 252, 10), (6, 264, 2), (6, 262, 2), (6, 280, 1), (6, 266, 2), (6, 281, 2), (1, 71, 2), (6, 237, 2), (1, 73, 2), (6, 239, 2), (1, 75, 2), (6, 241, 2), (1, 77, 1), (6, 243, 1), (1, 151, 2), (6, 268, 1), (1, 153, 2), (6, 283, 1), (6, 269, 2), (6, 284, 2), (6, 271, 2), (6, 286, 2), (6, 273, 1), (6, 288, 2), (1, 78, 2), (6, 244, 2), (1, 80, 1), (6, 246, 1), (1, 81, 1), (6, 247, 1), (6, 297, 1), (6, 274, 2), (6, 290, 2), (6, 276, 1), (6, 292, 2), (6, 277, 1), (6, 294, 1), (6, 278, 1), (6, 295, 1), (1, 82, 1), (6, 248, 1), (6, 302, 3), (6, 279, 1), (6, 296, 1), (6, 305, 3), (1, 186, 1), (1, 212, 1), (1, 187, 1), (1, 213, 1), (6, 308, 2), (1, 236, 1), (1, 286, 1), (1, 237, 1), (1, 287, 1), (6, 310, 2), (1, 188, 1), (1, 214, 1), (6, 312, 3), (1, 238, 1), (1, 288, 1), (1, 239, 1), (1, 289, 1), (6, 315, 4), (6, 323, 1), (6, 319, 2), (7, 0, 1), (6, 324, 2), (6, 321, 2), (7, 1, 1), (1, 303, 1), (1, 322, 1), (1, 304, 1), (1, 323, 1), (1, 305, 1), (1, 324, 1), (1, 306, 1), (1, 325, 1), (1, 361, 10), (1, 307, 1), (1, 326, 1), (1, 308, 1), (1, 327, 1), (1, 378, 2), (1, 371, 6), (1, 380, 1)]
end CKLaneG3.S.C0.B11


