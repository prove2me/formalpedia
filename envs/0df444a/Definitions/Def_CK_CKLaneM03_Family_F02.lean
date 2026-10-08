-- Prove2me | Definitions.Def_CK_CKLaneM03_Family_F02
-- name    : CK_CKLaneM03_Family_F02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T02:12:30.076793+00:00
-- url     : https://prove2.me/theorems/729c7565-8531-4c16-81c0-d3e166d6869e
-- title:
--   Courtade–Kumar proof module `CKLaneM03.Family.F02` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM03.Family.F02` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM03.Family.F02` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM03.Family.F02 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM03/Family/F02.lean)

import Definitions.Def_CK_CKLaneM03_Family_F02_q100

namespace CKLaneM03.EP
open CKLaneM03
namespace P0074
set_option maxRecDepth 200000 in
theorem leaves_sem : ∀ p ∈ leaves, Sem (ssBox p) :=
  sem_forall_cons l_50203000421531521520530430 (sem_forall_cons l_50203000421531521520530431 (sem_forall_cons l_5020300042153152152142042 (sem_forall_cons l_5020300042153152152142043 (sem_forall_cons l_50203000421531521521420520 (sem_forall_cons l_502030004215315215214205214 (sem_forall_cons l_50203000421531521521420530 (sem_forall_cons l_50203000421531521521420531 (sem_forall_cons l_5020300042153152152142142 (sem_forall_cons l_5020300042153152152142143 (sem_forall_cons l_502030004215315215214215204 (sem_forall_cons l_502030004215315215214215214 (sem_forall_cons l_50203000421531521521421530 (sem_forall_cons l_502030004215315215214215314 (sem_forall_cons l_5020300042153152152143042 (sem_forall_cons l_5020300042153152152143043 (sem_forall_cons l_50203000421531521521430520 (sem_forall_cons l_50203000421531521521430521 (sem_forall_cons l_5020300042153152152143053 (sem_forall_cons l_5020300042153152152143142 (sem_forall_cons l_5020300042153152152143143 (sem_forall_cons l_50203000421531521521431520 (sem_forall_cons l_50203000421531521521431521 (sem_forall_cons l_50203000421531521521431530 (sem_forall_cons l_50203000421531521521431531 (sem_forall_cons l_502030004215315215304204 (sem_forall_cons l_5020300042153152153042052 (sem_forall_cons l_5020300042153152153042053 (sem_forall_cons l_502030004215315215304214 (sem_forall_cons l_5020300042153152153042152 (sem_forall_cons l_5020300042153152153042153 (sem_forall_cons l_502030004215315215304314 (sem_forall_cons l_5020300042153152153043152 (sem_forall_cons l_5020300042153152153043153 (sem_forall_cons l_5020300042153152153052043 (sem_forall_cons l_5020300042153152153053143 (sem_forall_cons l_502030004215315215314204 (sem_forall_cons l_5020300042153152153142052 (sem_forall_cons l_5020300042153152153142053 (sem_forall_cons l_5020300042153152153142142 (sem_forall_cons l_5020300042153152153142143 (sem_forall_cons l_5020300042153152153142152 (sem_forall_cons l_5020300042153152153142153 (sem_forall_cons l_502030004215315215314304 (sem_forall_cons l_5020300042153152153143052 (sem_forall_cons l_5020300042153152153143053 (sem_forall_cons l_502030004215315215314314 (sem_forall_cons l_5020300042153152153143152 (sem_forall_cons l_5020300042153152153143153 (sem_forall_cons l_502030004215315314214 (sem_forall_cons l_5020300042153153142152 (sem_forall_cons l_5020300042153153142153 (sem_forall_cons l_502030004215315314314 (sem_forall_cons l_5020300042153153143152 (sem_forall_cons l_502030004215315315214204 (sem_forall_cons l_502030004215315315214205 (sem_forall_cons l_502030004215315315214214 (sem_forall_cons l_5020300042153153152142152 (sem_forall_cons l_5020300042153153152142153 (sem_forall_cons l_502030004215315315214314 (sem_forall_cons l_502030004215315315214315 (sem_forall_cons l_5020300042153153152152042 (sem_forall_cons l_5020300042153153152152043 (sem_forall_cons l_50203000421531531521521420 (sem_forall_cons l_50203000421531531521521421 (sem_forall_cons l_5020300042153153152152143 (sem_forall_cons l_5020300042153153152153142 (sem_forall_cons l_5020300042153153152153143 (sem_forall_cons l_50203000421531531521531531 (sem_forall_cons l_50203000421531531531421 (sem_forall_cons l_5020300042153153153152142 (sem_forall_cons l_50203000421531531531521521 sem_forall_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end P0074

end CKLaneM03.EP


