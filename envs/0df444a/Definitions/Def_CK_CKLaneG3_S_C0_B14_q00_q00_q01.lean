-- Prove2me | Definitions.Def_CK_CKLaneG3_S_C0_B14_q00_q00_q01
-- name    : CK_CKLaneG3_S_C0_B14_q00_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-09T19:38:21.592903+00:00
-- url     : https://prove2.me/theorems/6ea61596-6c84-4f1a-8d8c-62ed237d024c
-- title:
--   Courtade–Kumar proof module `CKLaneG3.S.C0.B14 (piece 1 of 4) (piece 1 of 3) (piece 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.S.C0.B14 (piece 1 of 4) (piece 1 of 3) (piece 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.S.C0.B14 (piece 1 of 4) (piece 1 of 3) (piece 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.S.C0.B14 (piece 1 of 4) (piece 1 of 3) (piece 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/S/C0/B14 (piece 1 of 4) (piece 1 of 3) (piece 2 of 3).lean)

import Definitions.Def_CK_CKLaneG3_S_C0_B14_q00_q00_q00

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneG3.S.C0.B14
open CKLaneD CKLaneG3
theorem SH_ok : ∀ S ∈ SH, ∀ x ∈ S, SLeafOK (sBox (id x)) :=
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB057.paths CKLaneE.NLSB057.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB059.paths CKLaneE.NLSB059.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB136.paths CKLaneE.NLSB136.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB137.paths CKLaneE.NLSB137.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB160.paths CKLaneE.NLSB160.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB162.paths CKLaneE.NLSB162.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB163.paths CKLaneE.NLSB163.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB164.paths CKLaneE.NLSB164.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB165.paths CKLaneE.NLSB165.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB167.paths CKLaneE.NLSB167.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB168.paths CKLaneE.NLSB168.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB169.paths CKLaneE.NLSB169.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB170.paths CKLaneE.NLSB170.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB171.paths CKLaneE.NLSB171.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB172.paths CKLaneE.NLSB172.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB173.paths CKLaneE.NLSB173.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB174.paths CKLaneE.NLSB174.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB175.paths CKLaneE.NLSB175.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB176.paths CKLaneE.NLSB176.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB177.paths CKLaneE.NLSB177.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB178.paths CKLaneE.NLSB178.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB179.paths CKLaneE.NLSB179.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB180.paths CKLaneE.NLSB180.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB181.paths CKLaneE.NLSB181.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB182.paths CKLaneE.NLSB182.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB183.paths CKLaneE.NLSB183.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB184.paths CKLaneE.NLSB184.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB185.paths CKLaneE.NLSB185.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB186.paths CKLaneE.NLSB186.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB187.paths CKLaneE.NLSB187.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB188.paths CKLaneE.NLSB188.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB189.paths CKLaneE.NLSB189.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB192.paths CKLaneE.NLSB192.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB193.paths CKLaneE.NLSB193.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB194.paths CKLaneE.NLSB194.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB195.paths CKLaneE.NLSB195.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB197.paths CKLaneE.NLSB197.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB199.paths CKLaneE.NLSB199.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB200.paths CKLaneE.NLSB200.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB201.paths CKLaneE.NLSB201.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB202.paths CKLaneE.NLSB202.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB203.paths CKLaneE.NLSB203.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB204.paths CKLaneE.NLSB204.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB205.paths CKLaneE.NLSB205.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB206.paths CKLaneE.NLSB206.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB207.paths CKLaneE.NLSB207.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB208.paths CKLaneE.NLSB208.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB209.paths CKLaneE.NLSB209.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB210.paths CKLaneE.NLSB210.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB211.paths CKLaneE.NLSB211.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB212.paths CKLaneE.NLSB212.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB213.paths CKLaneE.NLSB213.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB215.paths CKLaneE.NLSB215.family)
  (shards_cons (CKLaneE.SAdapt.family_sLeafOK CKLaneE.NLSB216.paths CKLaneE.NLSB216.family)
   shards_nil))))))))))))))))))))))))))))))))))))))))))))))))))))))

end CKLaneG3.S.C0.B14


