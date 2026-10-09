-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B14_q00_q00_q00_l01
-- name    : CK_CKLaneG3_S_C0_B14_q00_q00_q00_l01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-09T01:55:55.816534+00:00
-- url     : https://prove2.me/theorems/713601c2-a8bc-4df1-8a66-59b733aac610
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B14 (subtrees SH)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B14 (subtrees SH)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B14 (subtrees SH)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B14 (subtrees SH) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B14 (subtrees SH).lean)

import Definitions.Def_CK_CKLaneE_NLSB192__5
import Definitions.Def_CK_CKLaneE_NLSB197__5
import Definitions.Def_CK_CKLaneE_NLSB202__6
import Definitions.Def_CK_CKLaneE_NLSB208__5
import Definitions.Def_CK_CKLaneE_NLSB213__5

set_option autoImplicit false
set_option maxRecDepth 100000

/-! Sub-list 1 of `CKLaneG3.S.C0.B14.SH` (split by split_listdef.py; elements verbatim, in order). -/

namespace CKLaneG3.S.C0.B14

noncomputable def SH_l01 : List (List (List ℕ)) :=
  [CKLaneE.NLSB192.paths,
   CKLaneE.NLSB193.paths,
   CKLaneE.NLSB194.paths,
   CKLaneE.NLSB195.paths,
   CKLaneE.NLSB197.paths,
   CKLaneE.NLSB199.paths,
   CKLaneE.NLSB200.paths,
   CKLaneE.NLSB201.paths,
   CKLaneE.NLSB202.paths,
   CKLaneE.NLSB203.paths,
   CKLaneE.NLSB204.paths,
   CKLaneE.NLSB205.paths,
   CKLaneE.NLSB206.paths,
   CKLaneE.NLSB207.paths,
   CKLaneE.NLSB208.paths,
   CKLaneE.NLSB209.paths,
   CKLaneE.NLSB210.paths,
   CKLaneE.NLSB211.paths,
   CKLaneE.NLSB212.paths,
   CKLaneE.NLSB213.paths,
   CKLaneE.NLSB215.paths,
   CKLaneE.NLSB216.paths]

end CKLaneG3.S.C0.B14


