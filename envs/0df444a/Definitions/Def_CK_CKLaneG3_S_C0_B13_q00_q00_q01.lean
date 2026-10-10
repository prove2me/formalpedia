-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B13_q00_q00_q01
-- name    : CK_CKLaneG3_S_C0_B13_q00_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-09T14:51:53.911978+00:00
-- url     : https://prove2.me/theorems/201d9e44-f3a6-49b3-9543-bab450ffe7c6
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B13 (piece 1 of 4) (piece 1 of 4) (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B13 (piece 1 of 4) (piece 1 of 4) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B13 (piece 1 of 4) (piece 1 of 4) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B13 (piece 1 of 4) (piece 1 of 4) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B13 (piece 1 of 4) (piece 1 of 4) (piece 2 of 3).lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B13_q00_q00_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B13
open CKLaneD CKLaneG3
theorem SH_ok : ∀ S ∈ SH, ∀ x ∈ S, SLeafOK (sBox (id x)) :=
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB055.paths CKLaneE.NLSB055.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB057.paths CKLaneE.NLSB057.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB058.paths CKLaneE.NLSB058.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB059.paths CKLaneE.NLSB059.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB060.paths CKLaneE.NLSB060.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB061.paths CKLaneE.NLSB061.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB062.paths CKLaneE.NLSB062.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB063.paths CKLaneE.NLSB063.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB064.paths CKLaneE.NLSB064.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB121.paths CKLaneE.NLSB121.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB125.paths CKLaneE.NLSB125.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB126.paths CKLaneE.NLSB126.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB127.paths CKLaneE.NLSB127.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB128.paths CKLaneE.NLSB128.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB129.paths CKLaneE.NLSB129.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB130.paths CKLaneE.NLSB130.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB131.paths CKLaneE.NLSB131.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB132.paths CKLaneE.NLSB132.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB133.paths CKLaneE.NLSB133.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB134.paths CKLaneE.NLSB134.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB135.paths CKLaneE.NLSB135.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB136.paths CKLaneE.NLSB136.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB137.paths CKLaneE.NLSB137.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB138.paths CKLaneE.NLSB138.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB139.paths CKLaneE.NLSB139.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB140.paths CKLaneE.NLSB140.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB141.paths CKLaneE.NLSB141.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB142.paths CKLaneE.NLSB142.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB143.paths CKLaneE.NLSB143.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB144.paths CKLaneE.NLSB144.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB145.paths CKLaneE.NLSB145.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB146.paths CKLaneE.NLSB146.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB147.paths CKLaneE.NLSB147.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB148.paths CKLaneE.NLSB148.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB149.paths CKLaneE.NLSB149.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB150.paths CKLaneE.NLSB150.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB151.paths CKLaneE.NLSB151.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB152.paths CKLaneE.NLSB152.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB153.paths CKLaneE.NLSB153.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB154.paths CKLaneE.NLSB154.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB155.paths CKLaneE.NLSB155.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB156.paths CKLaneE.NLSB156.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB157.paths CKLaneE.NLSB157.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB158.paths CKLaneE.NLSB158.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB159.paths CKLaneE.NLSB159.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB160.paths CKLaneE.NLSB160.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB161.paths CKLaneE.NLSB161.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB162.paths CKLaneE.NLSB162.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB165.paths CKLaneE.NLSB165.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB166.paths CKLaneE.NLSB166.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB167.paths CKLaneE.NLSB167.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB189.paths CKLaneE.NLSB189.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB190.paths CKLaneE.NLSB190.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB191.paths CKLaneE.NLSB191.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB192.paths CKLaneE.NLSB192.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB193.paths CKLaneE.NLSB193.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB194.paths CKLaneE.NLSB194.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB195.paths CKLaneE.NLSB195.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB196.paths CKLaneE.NLSB196.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB197.paths CKLaneE.NLSB197.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB198.paths CKLaneE.NLSB198.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB199.paths CKLaneE.NLSB199.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB213.paths CKLaneE.NLSB213.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB214.paths CKLaneE.NLSB214.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB215.paths CKLaneE.NLSB215.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB216.paths CKLaneE.NLSB216.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB217.paths CKLaneE.NLSB217.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB221.paths CKLaneE.NLSB221.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB222.paths CKLaneE.NLSB222.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB226.paths CKLaneE.NLSB226.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB227.paths CKLaneE.NLSB227.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB228.paths CKLaneE.NLSB228.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB229.paths CKLaneE.NLSB229.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB230.paths CKLaneE.NLSB230.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB231.paths CKLaneE.NLSB231.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB232.paths CKLaneE.NLSB232.family)
   shards_nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end CKLaneG3.S.C0.B13


