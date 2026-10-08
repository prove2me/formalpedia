-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B12_q00_q00_q01
-- name    : CK_CKLaneG3_S_C0_B12_q00_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T21:48:09.091393+00:00
-- url     : https://prove2.me/theorems/0759e998-387a-41da-9e59-7421b45fd6a7
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B12 (piece 1 of 3) (piece 1 of 4) (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B12 (piece 1 of 3) (piece 1 of 4) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B12 (piece 1 of 3) (piece 1 of 4) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B12 (piece 1 of 3) (piece 1 of 4) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B12 (piece 1 of 3) (piece 1 of 4) (piece 2 of 3).lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B12_q00_q00_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B12
open CKLaneD CKLaneG3
theorem SH_ok : ∀ S ∈ SH, ∀ x ∈ S, SLeafOK (sBox (id x)) :=
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB071.paths CKLaneE.NLSB071.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB072.paths CKLaneE.NLSB072.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB073.paths CKLaneE.NLSB073.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB075.paths CKLaneE.NLSB075.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB076.paths CKLaneE.NLSB076.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB077.paths CKLaneE.NLSB077.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB078.paths CKLaneE.NLSB078.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB079.paths CKLaneE.NLSB079.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB081.paths CKLaneE.NLSB081.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB082.paths CKLaneE.NLSB082.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB083.paths CKLaneE.NLSB083.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB084.paths CKLaneE.NLSB084.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB085.paths CKLaneE.NLSB085.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB086.paths CKLaneE.NLSB086.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB087.paths CKLaneE.NLSB087.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB088.paths CKLaneE.NLSB088.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB089.paths CKLaneE.NLSB089.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB090.paths CKLaneE.NLSB090.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB091.paths CKLaneE.NLSB091.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB092.paths CKLaneE.NLSB092.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB093.paths CKLaneE.NLSB093.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB094.paths CKLaneE.NLSB094.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB095.paths CKLaneE.NLSB095.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB096.paths CKLaneE.NLSB096.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB097.paths CKLaneE.NLSB097.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB099.paths CKLaneE.NLSB099.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB100.paths CKLaneE.NLSB100.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB101.paths CKLaneE.NLSB101.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB102.paths CKLaneE.NLSB102.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB103.paths CKLaneE.NLSB103.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB104.paths CKLaneE.NLSB104.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB105.paths CKLaneE.NLSB105.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB106.paths CKLaneE.NLSB106.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB107.paths CKLaneE.NLSB107.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB108.paths CKLaneE.NLSB108.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB109.paths CKLaneE.NLSB109.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB110.paths CKLaneE.NLSB110.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB111.paths CKLaneE.NLSB111.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB112.paths CKLaneE.NLSB112.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB113.paths CKLaneE.NLSB113.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB114.paths CKLaneE.NLSB114.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB115.paths CKLaneE.NLSB115.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB116.paths CKLaneE.NLSB116.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB117.paths CKLaneE.NLSB117.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB118.paths CKLaneE.NLSB118.family)
   shards_nil)))))))))))))))))))))))))))))))))))))))))))))

end CKLaneG3.S.C0.B12


