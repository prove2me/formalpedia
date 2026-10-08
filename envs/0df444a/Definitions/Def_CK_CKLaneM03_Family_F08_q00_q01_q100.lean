-- Prove2me | Definitions.Def_CK_CKLaneM03_Family_F08_q00_q01_q100
-- name    : CK_CKLaneM03_Family_F08_q00_q01_q100
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T04:09:11.002986+00:00
-- url     : https://prove2.me/theorems/dcaff5b8-197b-4311-b5d4-7d805b0e7800
-- title:
--   Courtade–Kumar proof module `CKLaneM03.Family.F08 (piece 1 of 4) (piece 2 of 4) (piece 1 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM03.Family.F08 (piece 1 of 4) (piece 2 of 4) (piece 1 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM03.Family.F08 (piece 1 of 4) (piece 2 of 4) (piece 1 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM03.Family.F08 (piece 1 of 4) (piece 2 of 4) (piece 1 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM03/Family/F08 (piece 1 of 4) (piece 2 of 4) (piece 1 of 5).lean)

import Definitions.Def_CK_CKLaneM03_Family_F08_q00_q01_q01


namespace CKLaneM03.EP
open CKLaneM03
namespace P0202
set_option maxRecDepth 200000 in
theorem leaves_sem : ∀ p ∈ leaves, Sem (ssBox p) :=
  sem_forall_cons l_503001043152042042 (sem_forall_cons l_503001043152042043 (sem_forall_cons l_50300104315204205204 (sem_forall_cons l_50300104315204205205 (sem_forall_cons l_50300104315204205214 (sem_forall_cons l_50300104315204205215 (sem_forall_cons l_50300104315204205304 (sem_forall_cons l_50300104315204205305 (sem_forall_cons l_50300104315204205314 (sem_forall_cons l_50300104315204205315 (sem_forall_cons l_5030010431520421420 (sem_forall_cons l_5030010431520421421 (sem_forall_cons l_503001043152042143 (sem_forall_cons l_50300104315204215204 (sem_forall_cons l_503001043152042152052 (sem_forall_cons l_503001043152042152053 (sem_forall_cons l_50300104315204215214 (sem_forall_cons l_503001043152042152152 (sem_forall_cons l_503001043152042152153 (sem_forall_cons l_50300104315204215304 (sem_forall_cons l_50300104315204215305 (sem_forall_cons l_50300104315204215314 (sem_forall_cons l_503001043152042153152 (sem_forall_cons l_503001043152042153153 (sem_forall_cons l_503001043152043042 (sem_forall_cons l_503001043152043043 (sem_forall_cons l_5030010431520430520 (sem_forall_cons l_5030010431520430521 (sem_forall_cons l_5030010431520430530 (sem_forall_cons l_5030010431520430531 (sem_forall_cons l_503001043152043142 (sem_forall_cons l_503001043152043143 (sem_forall_cons l_50300104315204315204 (sem_forall_cons l_50300104315204315205 (sem_forall_cons l_50300104315204315214 (sem_forall_cons l_50300104315204315215 (sem_forall_cons l_5030010431520431530 (sem_forall_cons l_50300104315204315314 (sem_forall_cons l_50300104315204315315 (sem_forall_cons l_503001043152052042042 (sem_forall_cons l_503001043152052042043 (sem_forall_cons l_503001043152052042052 (sem_forall_cons l_503001043152052042053 (sem_forall_cons l_503001043152052042142 (sem_forall_cons l_503001043152052042143 (sem_forall_cons l_503001043152052042152 (sem_forall_cons l_503001043152052042153 (sem_forall_cons l_503001043152052043042 (sem_forall_cons l_503001043152052043043 (sem_forall_cons l_503001043152052043052 (sem_forall_cons l_503001043152052043053 (sem_forall_cons l_503001043152052043142 (sem_forall_cons l_503001043152052043143 (sem_forall_cons l_503001043152052043152 (sem_forall_cons l_503001043152052043153 (sem_forall_cons l_50300104315205205204204 (sem_forall_cons l_50300104315205205204205 (sem_forall_cons l_50300104315205205204214 (sem_forall_cons l_50300104315205205204215 (sem_forall_cons l_5030010431520520520430 (sem_forall_cons l_5030010431520520520431 (sem_forall_cons l_503001043152052052052042 (sem_forall_cons l_503001043152052052052043 (sem_forall_cons l_503001043152052052052052 (sem_forall_cons l_503001043152052052052053 (sem_forall_cons l_503001043152052052052142 (sem_forall_cons l_503001043152052052052143 (sem_forall_cons l_503001043152052052052152 (sem_forall_cons l_503001043152052052052153 (sem_forall_cons l_50300104315205205205304 (sem_forall_cons l_503001043152052052053052 (sem_forall_cons l_503001043152052052053053 (sem_forall_cons l_503001043152052052053142 (sem_forall_cons l_503001043152052052053143 (sem_forall_cons l_503001043152052052053152 (sem_forall_cons l_503001043152052052053153 (sem_forall_cons l_50300104315205205214204 (sem_forall_cons l_50300104315205205214205 (sem_forall_cons l_50300104315205205214214 (sem_forall_cons l_503001043152052052142152 (sem_forall_cons l_503001043152052052142153 (sem_forall_cons l_50300104315205205214304 (sem_forall_cons l_50300104315205205214305 (sem_forall_cons l_50300104315205205214314 (sem_forall_cons l_50300104315205205214315 (sem_forall_cons l_503001043152052052152042 (sem_forall_cons l_503001043152052052152043 (sem_forall_cons l_5030010431520520521520520 (sem_forall_cons l_5030010431520520521520521 (sem_forall_cons l_503001043152052052152053 (sem_forall_cons l_503001043152052052152142 (sem_forall_cons l_503001043152052052152143 (sem_forall_cons l_5030010431520520521521530 (sem_forall_cons l_503001043152052052153042 (sem_forall_cons l_503001043152052052153043 (sem_forall_cons l_503001043152052052153052 (sem_forall_cons l_503001043152052052153053 (sem_forall_cons l_503001043152052052153142 (sem_forall_cons l_503001043152052052153143 (sem_forall_cons l_503001043152052052153152 (sem_forall_cons l_503001043152052052153153 sem_forall_nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end P0202

namespace P0203

end P0203
end CKLaneM03.EP


