-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B13_q00_q00_q00_l02
-- name    : CK_CKLaneG3_S_C0_B13_q00_q00_q00_l02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T19:20:07.108921+00:00
-- url     : https://prove2.me/theorems/6b9beb17-6159-4834-94c1-08c65fd0e340
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B13 (subtrees SH)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B13 (subtrees SH)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B13 (subtrees SH)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B13 (subtrees SH) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B13 (subtrees SH).lean)

import Definitions.Def_CK_CKLaneE_NLSB213__5
import Definitions.Def_CK_CKLaneE_NLSB218__7
import Definitions.Def_CK_CKLaneE_NLSB225__6
import Definitions.Def_CK_CKLaneE_NLSB231__2

set_option autoImplicit false
set_option maxRecDepth 100000

/-! Sub-list 2 of `CKLaneG3.S.C0.B13.SH` (split by split_listdef.py; elements verbatim, in order). -/

namespace CKLaneG3.S.C0.B13

noncomputable def SH_l02 : List (List (List ℕ)) :=
  [CKLaneE.NLSB215.paths,
   CKLaneE.NLSB216.paths,
   CKLaneE.NLSB217.paths,
   CKLaneE.NLSB221.paths,
   CKLaneE.NLSB222.paths,
   CKLaneE.NLSB226.paths,
   CKLaneE.NLSB227.paths,
   CKLaneE.NLSB228.paths,
   CKLaneE.NLSB229.paths,
   CKLaneE.NLSB230.paths,
   CKLaneE.NLSB231.paths,
   CKLaneE.NLSB232.paths]

end CKLaneG3.S.C0.B13


