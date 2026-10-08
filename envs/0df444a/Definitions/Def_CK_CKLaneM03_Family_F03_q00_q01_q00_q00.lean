-- Prove2me | Definitions.Def_CK_CKLaneM03_Family_F03_q00_q01_q00_q00
-- name    : CK_CKLaneM03_Family_F03_q00_q01_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T01:30:57.204218+00:00
-- url     : https://prove2.me/theorems/9c9de110-3f00-433c-8b78-76a915443c48
-- title:
--   Courtade–Kumar proof module `CKLaneM03.Family.F03 (piece 1 of 4) (piece 2 of 4) (piece 1 of 3) (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM03.Family.F03 (piece 1 of 4) (piece 2 of 4) (piece 1 of 3) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM03.Family.F03 (piece 1 of 4) (piece 2 of 4) (piece 1 of 3) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM03.Family.F03 (piece 1 of 4) (piece 2 of 4) (piece 1 of 3) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM03/Family/F03 (piece 1 of 4) (piece 2 of 4) (piece 1 of 3) (piece 1 of 3).lean)

import Definitions.Def_CK_CKLaneM03_Family_F03_q00_q00



namespace CKLaneM03.EP
open CKLaneM03
namespace P0075
set_option maxRecDepth 200000 in
theorem leaves_sem : ∀ p ∈ leaves, Sem (ssBox p) :=
  sem_forall_cons l_5020300142042042 (sem_forall_cons l_5020300142042043 (sem_forall_cons l_502030014204205204 (sem_forall_cons l_5020300142042052052 (sem_forall_cons l_5020300142042052053 (sem_forall_cons l_502030014204205214 (sem_forall_cons l_5020300142042052152 (sem_forall_cons l_5020300142042052153 (sem_forall_cons l_502030014204205304 (sem_forall_cons l_5020300142042053052 (sem_forall_cons l_5020300142042053053 (sem_forall_cons l_502030014204205314 (sem_forall_cons l_5020300142042053152 (sem_forall_cons l_5020300142042053153 (sem_forall_cons l_50203001420421420 (sem_forall_cons l_50203001420421421 (sem_forall_cons l_5020300142042143 (sem_forall_cons l_502030014204215204 (sem_forall_cons l_5020300142042152052 (sem_forall_cons l_5020300142042152053 (sem_forall_cons l_5020300142042152142 (sem_forall_cons l_5020300142042152143 (sem_forall_cons l_50203001420421521520 (sem_forall_cons l_50203001420421521521 (sem_forall_cons l_5020300142042152153 (sem_forall_cons l_502030014204215304 (sem_forall_cons l_5020300142042153052 (sem_forall_cons l_5020300142042153053 (sem_forall_cons l_502030014204215314 (sem_forall_cons l_5020300142042153152 (sem_forall_cons l_5020300142042153153 (sem_forall_cons l_5020300142043042 (sem_forall_cons l_5020300142043043 (sem_forall_cons l_502030014204305204 (sem_forall_cons l_502030014204305205 (sem_forall_cons l_502030014204305214 (sem_forall_cons l_502030014204305215 (sem_forall_cons l_50203001420430530 (sem_forall_cons l_50203001420430531 (sem_forall_cons l_5020300142043142 (sem_forall_cons l_5020300142043143 (sem_forall_cons l_502030014204315204 (sem_forall_cons l_5020300142043152052 (sem_forall_cons l_5020300142043152053 (sem_forall_cons l_502030014204315214 (sem_forall_cons l_5020300142043152152 (sem_forall_cons l_5020300142043152153 (sem_forall_cons l_502030014204315304 (sem_forall_cons l_502030014204315305 (sem_forall_cons l_502030014204315314 (sem_forall_cons l_502030014204315315 (sem_forall_cons l_50203001420520420420 (sem_forall_cons l_502030014205204204214 (sem_forall_cons l_502030014205204204215 (sem_forall_cons l_50203001420520420430 (sem_forall_cons l_50203001420520420431 (sem_forall_cons l_5020300142052042052024 (sem_forall_cons l_50203001420520420520250 (sem_forall_cons l_502030014205204205202512 (sem_forall_cons l_502030014205204205202513 (sem_forall_cons l_5020300142052042052034 (sem_forall_cons l_50203001420520420520350 (sem_forall_cons l_50203001420520420520351 (sem_forall_cons l_5020300142052042052124 (sem_forall_cons l_502030014205204205212502 (sem_forall_cons l_502030014205204205212503 (sem_forall_cons l_502030014205204205212512 (sem_forall_cons l_502030014205204205212513 (sem_forall_cons l_5020300142052042052134 (sem_forall_cons l_50203001420520420521350 (sem_forall_cons l_502030014205204205213512 (sem_forall_cons l_502030014205204205213513 (sem_forall_cons l_5020300142052042053042 (sem_forall_cons l_5020300142052042053043 (sem_forall_cons l_50203001420520420530520 (sem_forall_cons l_50203001420520420530521 (sem_forall_cons l_5020300142052042053053 (sem_forall_cons l_5020300142052042053142 (sem_forall_cons l_5020300142052042053143 (sem_forall_cons l_50203001420520420531520 (sem_forall_cons l_50203001420520420531521 (sem_forall_cons l_50203001420520420531530 (sem_forall_cons l_50203001420520420531531 (sem_forall_cons l_502030014205204214204 (sem_forall_cons l_5020300142052042142052 (sem_forall_cons l_5020300142052042142053 (sem_forall_cons l_502030014205204214214 (sem_forall_cons l_5020300142052042142152 (sem_forall_cons l_5020300142052042142153 (sem_forall_cons l_50203001420520421430 (sem_forall_cons l_502030014205204214314 (sem_forall_cons l_502030014205204214315 (sem_forall_cons l_5020300142052042152024 (sem_forall_cons l_502030014205204215202502 (sem_forall_cons l_502030014205204215202503 (sem_forall_cons l_502030014205204215202512 (sem_forall_cons l_502030014205204215202513 (sem_forall_cons l_5020300142052042152034 (sem_forall_cons l_502030014205204215203502 (sem_forall_cons l_502030014205204215203503 (sem_forall_cons l_502030014205204215203512 (sem_forall_cons l_502030014205204215203513 (sem_forall_cons l_50203001420520421521240 (sem_forall_cons l_50203001420520421521241 (sem_forall_cons l_502030014205204215212503 (sem_forall_cons l_5020300142052042152134 (sem_forall_cons l_502030014205204215213502 (sem_forall_cons l_502030014205204215213503 (sem_forall_cons l_502030014205204215213512 (sem_forall_cons l_502030014205204215213513 sem_forall_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end P0075

namespace P0076

end P0076
end CKLaneM03.EP


