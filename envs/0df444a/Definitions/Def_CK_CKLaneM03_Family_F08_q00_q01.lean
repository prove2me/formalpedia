-- Prove2me | Definitions.Def_CK_CKLaneM03_Family_F08_q00_q01
-- name    : CK_CKLaneM03_Family_F08_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T06:57:31.976551+00:00
-- url     : https://prove2.me/theorems/f5437dae-e4da-4919-86c0-d78cd4d7e57d
-- title:
--   Courtade–Kumar proof module `CKLaneM03.Family.F08 (piece 1 of 4) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM03.Family.F08 (piece 1 of 4) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM03.Family.F08 (piece 1 of 4) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM03.Family.F08 (piece 1 of 4) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM03/Family/F08 (piece 1 of 4) (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneM03_Family_F08_q00_q01_q03

namespace CKLaneM03.EP
open CKLaneM03
namespace P0204
set_option maxRecDepth 200000 in
theorem leaves_sem : ∀ p ∈ leaves, Sem (ssBox p) :=
  sem_forall_cons l_50300104315205215314204 (sem_forall_cons l_503001043152052153142052 (sem_forall_cons l_503001043152052153142053 (sem_forall_cons l_50300104315205215314214 (sem_forall_cons l_503001043152052153142152 (sem_forall_cons l_503001043152052153142153 (sem_forall_cons l_50300104315205215314304 (sem_forall_cons l_50300104315205215314305 (sem_forall_cons l_50300104315205215314314 (sem_forall_cons l_50300104315205215314315 (sem_forall_cons l_503001043152052153152042 (sem_forall_cons l_503001043152052153152043 (sem_forall_cons l_503001043152052153152142 (sem_forall_cons l_503001043152052153152143 (sem_forall_cons l_503001043152052153153042 (sem_forall_cons l_503001043152052153153043 (sem_forall_cons l_503001043152052153153052 (sem_forall_cons l_503001043152052153153053 (sem_forall_cons l_503001043152052153153142 (sem_forall_cons l_503001043152052153153143 (sem_forall_cons l_503001043152052153153153 sem_forall_nil))))))))))))))))))))

end P0204

namespace P0205

end P0205
end CKLaneM03.EP


