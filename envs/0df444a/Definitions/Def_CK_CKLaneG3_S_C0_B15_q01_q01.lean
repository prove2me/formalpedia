-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B15_q01_q01
-- name    : CK_CKLaneG3_S_C0_B15_q01_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-09T01:47:39.4455+00:00
-- url     : https://prove2.me/theorems/233131a2-11bc-4196-a819-a5e30deda67e
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B15 (piece 2 of 4) (piece 2 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B15 (piece 2 of 4) (piece 2 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B15 (piece 2 of 4) (piece 2 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B15 (piece 2 of 4) (piece 2 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B15 (piece 2 of 4) (piece 2 of 5).lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B15_q01_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B15
open CKLaneD CKLaneG3
/-- chunk `503001043`: 0 label-0 leaves. -/
theorem c_503001043 : ∀ q ∈ CKLaneG3.S.Chunk.C_503001043.t.leavesR [3, 4, 0, 1, 0, 0, 3, 0, 5], q.2 = 0 → SLeafOK (sBox q.1) :=
  sub_family_of_none (Q := fun p => SLeafOK (sBox p)) CKLaneG3.S.Chunk.C_503001043.t 0 [3, 4, 0, 1, 0, 0, 3, 0, 5] (by decide +kernel)

end CKLaneG3.S.C0.B15


