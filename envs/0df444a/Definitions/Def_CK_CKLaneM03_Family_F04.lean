-- Prove2me | Definitions.Def_CK_CKLaneM03_Family_F04
-- name    : CK_CKLaneM03_Family_F04
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T08:29:41.431241+00:00
-- url     : https://prove2.me/theorems/d5efb25a-6029-4ddc-80c6-b7d09eed5762
-- title:
--   Courtade–Kumar proof module `CKLaneM03.Family.F04` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM03.Family.F04` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM03.Family.F04` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM03.Family.F04 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM03/Family/F04.lean)

import Definitions.Def_CK_CKLaneM03_Family_F04_q100

namespace CKLaneM03.EP
open CKLaneM03
namespace P0124
set_option maxRecDepth 200000 in
theorem leaves_sem : ∀ p ∈ leaves, Sem (ssBox p) :=
  sem_forall_cons l_502030114304304042 (sem_forall_cons l_502030114304304043 (sem_forall_cons l_502030114304304052 (sem_forall_cons l_502030114304304053 (sem_forall_cons l_502030114304304142 (sem_forall_cons l_502030114304304143 (sem_forall_cons l_502030114304304152 (sem_forall_cons l_502030114304304153 (sem_forall_cons l_50203011430430502402 (sem_forall_cons l_50203011430430502403 (sem_forall_cons l_50203011430430503402 (sem_forall_cons l_50203011430430503403 (sem_forall_cons l_50203011430430503412 (sem_forall_cons l_50203011430430503413 (sem_forall_cons l_502030114304314042 (sem_forall_cons l_502030114304314043 (sem_forall_cons l_5020301143043140520 (sem_forall_cons l_5020301143043140521 (sem_forall_cons l_502030114304314053 (sem_forall_cons l_502030114304314142 (sem_forall_cons l_502030114304314143 (sem_forall_cons l_5020301143043141520 (sem_forall_cons l_5020301143043141530 (sem_forall_cons l_5020301143043141531 (sem_forall_cons l_502030114314204204 (sem_forall_cons l_502030114314204304 (sem_forall_cons l_502030114314204314 (sem_forall_cons l_502030114314304042 (sem_forall_cons l_502030114314304043 (sem_forall_cons l_5020301143143040530 (sem_forall_cons l_5020301143143040531 (sem_forall_cons l_502030114314304142 (sem_forall_cons l_502030114314304143 (sem_forall_cons l_502030114314314043 (sem_forall_cons l_503000142042142 (sem_forall_cons l_50300014204215214 (sem_forall_cons l_503000142042152152 (sem_forall_cons l_503000142042152153 (sem_forall_cons l_503000142052124124 (sem_forall_cons l_5030001420521241250 (sem_forall_cons l_5030001420521241251 (sem_forall_cons l_503000142052124134 (sem_forall_cons l_5030001420521241351 (sem_forall_cons l_50300014205212512402 (sem_forall_cons l_50300014205212512412 (sem_forall_cons l_50300014205212512413 (sem_forall_cons l_503000142052125125024 (sem_forall_cons l_50300014205212512502512 (sem_forall_cons l_50300014205212512502513 (sem_forall_cons l_5030001420521251251240 (sem_forall_cons l_5030001420521251251241 (sem_forall_cons l_50300014205212512512502 (sem_forall_cons l_50300014205212512512503 (sem_forall_cons l_50300014205212512512512 (sem_forall_cons l_50300014205212512512513 (sem_forall_cons l_503000142052125125134 (sem_forall_cons l_50300014205212512513502 (sem_forall_cons l_50300014205212512513503 (sem_forall_cons l_50300014205212512513512 (sem_forall_cons l_50300014205212512513513 (sem_forall_cons l_50300014205212513412 (sem_forall_cons l_503000142052125135124 (sem_forall_cons l_50300014205212513512512 (sem_forall_cons l_5030001421420420 (sem_forall_cons l_5030001421420421 (sem_forall_cons l_503000142142043 (sem_forall_cons l_50300014214205204 (sem_forall_cons l_503000142142052052 (sem_forall_cons l_503000142142052053 (sem_forall_cons l_50300014214205214 (sem_forall_cons l_503000142142052152 (sem_forall_cons l_503000142142052153 (sem_forall_cons l_50300014214205304 (sem_forall_cons l_50300014214205305 (sem_forall_cons l_50300014214205314 (sem_forall_cons l_503000142142053152 (sem_forall_cons l_503000142142053153 (sem_forall_cons l_5030001421421420 (sem_forall_cons l_5030001421421421 (sem_forall_cons l_5030001421421430 (sem_forall_cons l_5030001421421431 (sem_forall_cons l_50300014214215204 (sem_forall_cons l_503000142142152052 (sem_forall_cons l_503000142142152053 (sem_forall_cons l_503000142142152142 (sem_forall_cons l_503000142142152143 (sem_forall_cons l_503000142142152152 (sem_forall_cons l_503000142142152153 (sem_forall_cons l_50300014214215304 (sem_forall_cons l_503000142142153052 (sem_forall_cons l_503000142142153053 (sem_forall_cons l_50300014214215314 (sem_forall_cons l_503000142142153152 (sem_forall_cons l_503000142142153153 (sem_forall_cons l_503000142143042 (sem_forall_cons l_50300014214305214 (sem_forall_cons l_50300014214305215 (sem_forall_cons l_5030001421431420 (sem_forall_cons l_5030001421431421 (sem_forall_cons l_5030001421431430 (sem_forall_cons l_5030001421431431 (sem_forall_cons l_50300014214315204 (sem_forall_cons l_50300014214315205 (sem_forall_cons l_50300014214315214 (sem_forall_cons l_503000142143152152 (sem_forall_cons l_503000142143152153 (sem_forall_cons l_50300014214315304 (sem_forall_cons l_50300014214315305 (sem_forall_cons l_50300014214315314 (sem_forall_cons l_50300014214315315 sem_forall_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end P0124

end CKLaneM03.EP


