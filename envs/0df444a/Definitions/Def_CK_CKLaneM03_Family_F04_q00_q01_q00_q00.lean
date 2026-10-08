-- Prove2me | Definitions.Def_CK_CKLaneM03_Family_F04_q00_q01_q00_q00
-- name    : CK_CKLaneM03_Family_F04_q00_q01_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T00:33:23.986922+00:00
-- url     : https://prove2.me/theorems/343f581c-6601-4de6-a0d8-50a1bd2a697c
-- title:
--   Courtade–Kumar proof module `CKLaneM03.Family.F04 (piece 1 of 4) (piece 2 of 4) (piece 1 of 3) (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM03.Family.F04 (piece 1 of 4) (piece 2 of 4) (piece 1 of 3) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM03.Family.F04 (piece 1 of 4) (piece 2 of 4) (piece 1 of 3) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM03.Family.F04 (piece 1 of 4) (piece 2 of 4) (piece 1 of 3) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM03/Family/F04 (piece 1 of 4) (piece 2 of 4) (piece 1 of 3) (piece 1 of 3).lean)

import Definitions.Def_CK_CKLaneM03_Family_F04_q00_q00



namespace CKLaneM03.EP
open CKLaneM03
namespace P0100
set_option maxRecDepth 200000 in
theorem leaves_sem : ∀ p ∈ leaves, Sem (ssBox p) :=
  sem_forall_cons l_50203001431521421420 (sem_forall_cons l_502030014315214214214 (sem_forall_cons l_502030014315214214215 (sem_forall_cons l_50203001431521421430 (sem_forall_cons l_50203001431521421431 (sem_forall_cons l_5020300143152142152042 (sem_forall_cons l_5020300143152142152043 (sem_forall_cons l_502030014315214215205204 (sem_forall_cons l_502030014315214215205205 (sem_forall_cons l_502030014315214215205214 (sem_forall_cons l_50203001431521421520530 (sem_forall_cons l_502030014315214215205314 (sem_forall_cons l_502030014315214215205315 (sem_forall_cons l_5020300143152142152142 (sem_forall_cons l_5020300143152142152143 (sem_forall_cons l_502030014315214215215204 (sem_forall_cons l_502030014315214215215304 (sem_forall_cons l_502030014315214215215314 (sem_forall_cons l_5020300143152142153042 (sem_forall_cons l_5020300143152142153043 (sem_forall_cons l_50203001431521421530520 (sem_forall_cons l_50203001431521421530521 (sem_forall_cons l_50203001431521421530530 (sem_forall_cons l_50203001431521421530531 (sem_forall_cons l_5020300143152142153142 (sem_forall_cons l_5020300143152142153143 (sem_forall_cons l_50203001431521421531520 (sem_forall_cons l_502030014315214215315214 (sem_forall_cons l_502030014315214215315215 (sem_forall_cons l_50203001431521421531530 (sem_forall_cons l_50203001431521421531531 (sem_forall_cons l_5020300143152143042 (sem_forall_cons l_5020300143152143043 (sem_forall_cons l_502030014315214305204 (sem_forall_cons l_5020300143152143052052 (sem_forall_cons l_5020300143152143052053 (sem_forall_cons l_502030014315214305214 (sem_forall_cons l_5020300143152143052152 (sem_forall_cons l_5020300143152143052153 (sem_forall_cons l_502030014315214305304 (sem_forall_cons l_5020300143152143053052 (sem_forall_cons l_5020300143152143053053 (sem_forall_cons l_502030014315214305314 (sem_forall_cons l_5020300143152143053152 (sem_forall_cons l_5020300143152143053153 (sem_forall_cons l_50203001431521431420 (sem_forall_cons l_50203001431521431421 (sem_forall_cons l_5020300143152143143 (sem_forall_cons l_502030014315214315204 (sem_forall_cons l_5020300143152143152052 (sem_forall_cons l_5020300143152143152053 (sem_forall_cons l_5020300143152143152142 (sem_forall_cons l_5020300143152143152143 (sem_forall_cons l_50203001431521431521520 (sem_forall_cons l_50203001431521431521521 (sem_forall_cons l_5020300143152143152153 (sem_forall_cons l_502030014315214315304 (sem_forall_cons l_5020300143152143153052 (sem_forall_cons l_5020300143152143153053 (sem_forall_cons l_502030014315214315314 (sem_forall_cons l_5020300143152143153152 (sem_forall_cons l_5020300143152143153153 (sem_forall_cons l_502030014315215204204204 (sem_forall_cons l_502030014315215204204304 (sem_forall_cons l_502030014315215204204314 (sem_forall_cons l_502030014315215204214304 (sem_forall_cons l_502030014315215204304204 (sem_forall_cons l_5020300143152152043042052 (sem_forall_cons l_5020300143152152043042053 (sem_forall_cons l_502030014315215204304214 (sem_forall_cons l_5020300143152152043042153 (sem_forall_cons l_502030014315215204304304 (sem_forall_cons l_502030014315215204304305 (sem_forall_cons l_502030014315215204304314 (sem_forall_cons l_502030014315215204304315 (sem_forall_cons l_5020300143152152043053043 (sem_forall_cons l_502030014315215204314204 (sem_forall_cons l_502030014315215204314214 (sem_forall_cons l_502030014315215204314304 (sem_forall_cons l_5020300143152152043143053 (sem_forall_cons l_502030014315215204314314 (sem_forall_cons l_502030014315215214304304 (sem_forall_cons l_502030014315215214304314 (sem_forall_cons l_50203001431521530420420 (sem_forall_cons l_502030014315215304204214 (sem_forall_cons l_502030014315215304204215 (sem_forall_cons l_50203001431521530420430 (sem_forall_cons l_50203001431521530420431 (sem_forall_cons l_5020300143152153042052042 (sem_forall_cons l_5020300143152153042052043 (sem_forall_cons l_5020300143152153042052142 (sem_forall_cons l_5020300143152153042052143 (sem_forall_cons l_5020300143152153042053042 (sem_forall_cons l_5020300143152153042053043 (sem_forall_cons l_5020300143152153042053053 (sem_forall_cons l_5020300143152153042053142 (sem_forall_cons l_5020300143152153042053143 (sem_forall_cons l_502030014315215304214204 (sem_forall_cons l_502030014315215304214205 (sem_forall_cons l_502030014315215304214214 (sem_forall_cons l_5020300143152153042142152 (sem_forall_cons l_5020300143152153042142153 (sem_forall_cons l_50203001431521530421430 (sem_forall_cons l_502030014315215304214314 (sem_forall_cons l_502030014315215304214315 (sem_forall_cons l_5020300143152153042152043 (sem_forall_cons l_5020300143152153042153042 (sem_forall_cons l_5020300143152153042153043 (sem_forall_cons l_5020300143152153042153143 sem_forall_nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end P0100

namespace P0101

end P0101
end CKLaneM03.EP


