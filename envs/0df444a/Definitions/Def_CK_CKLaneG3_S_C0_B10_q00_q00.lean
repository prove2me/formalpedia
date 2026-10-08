-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B10_q00_q00
-- name    : CK_CKLaneG3_S_C0_B10_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T22:39:01.339845+00:00
-- url     : https://prove2.me/theorems/b400b6f9-e1c1-4f4d-a7f3-b624cd37bf43
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B10 (piece 1 of 4) (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B10 (piece 1 of 4) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B10 (piece 1 of 4) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B10 (piece 1 of 4) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B10 (piece 1 of 4) (piece 1 of 4).lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B10_q00_q00_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B10
open CKLaneD CKLaneG3
theorem SH_ok : ∀ S ∈ SH, ∀ x ∈ S, SLeafOK (sBox (id x)) :=
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB064.paths CKLaneE.NLSB064.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB065.paths CKLaneE.NLSB065.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB066.paths CKLaneE.NLSB066.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB067.paths CKLaneE.NLSB067.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB068.paths CKLaneE.NLSB068.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB069.paths CKLaneE.NLSB069.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB070.paths CKLaneE.NLSB070.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB071.paths CKLaneE.NLSB071.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB072.paths CKLaneE.NLSB072.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB073.paths CKLaneE.NLSB073.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB086.paths CKLaneE.NLSB086.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB087.paths CKLaneE.NLSB087.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB089.paths CKLaneE.NLSB089.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB090.paths CKLaneE.NLSB090.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB093.paths CKLaneE.NLSB093.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB095.paths CKLaneE.NLSB095.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB096.paths CKLaneE.NLSB096.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB097.paths CKLaneE.NLSB097.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB098.paths CKLaneE.NLSB098.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB099.paths CKLaneE.NLSB099.family)
   shards_nil))))))))))))))))))))

end CKLaneG3.S.C0.B10


