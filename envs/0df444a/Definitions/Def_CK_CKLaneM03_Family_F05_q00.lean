-- Prove2me | Definitions.Def_CK_CKLaneM03_Family_F05_q00
-- name    : CK_CKLaneM03_Family_F05_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T06:23:26.337987+00:00
-- url     : https://prove2.me/theorems/64aea0da-c748-4f29-9ceb-280494714e0f
-- title:
--   Courtade–Kumar proof module `CKLaneM03.Family.F05 (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM03.Family.F05 (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM03.Family.F05 (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM03.Family.F05 (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM03/Family/F05 (piece 1 of 4).lean)

import Definitions.Def_CK_CKLaneM03_Family_F05_q00_q03

namespace CKLaneM03.EP
open CKLaneM03
namespace P0132
set_option maxRecDepth 200000 in
theorem leaves_sem : ∀ p ∈ leaves, Sem (ssBox p) :=
  sem_forall_cons l_503000142153042142 (sem_forall_cons l_503000142153042152 (sem_forall_cons l_50300014215305214214 (sem_forall_cons l_50300014215305214215 (sem_forall_cons l_503000142153052152124 (sem_forall_cons l_503000142153052152125 (sem_forall_cons l_503000142153052152134 (sem_forall_cons l_503000142153052152135 (sem_forall_cons l_503000142153142042 (sem_forall_cons l_503000142153142043 (sem_forall_cons l_5030001421531420520 (sem_forall_cons l_5030001421531420521 (sem_forall_cons l_503000142153142053 (sem_forall_cons l_503000142153142142 (sem_forall_cons l_503000142153142143 (sem_forall_cons l_5030001421531421520 (sem_forall_cons l_5030001421531421521 (sem_forall_cons l_5030001421531421530 (sem_forall_cons l_5030001421531421531 (sem_forall_cons l_503000142153143042 (sem_forall_cons l_503000142153143052 (sem_forall_cons l_503000142153143142 (sem_forall_cons l_503000142153143143 (sem_forall_cons l_503000142153143152 (sem_forall_cons l_503000142153143153 (sem_forall_cons l_50300014215315204204 (sem_forall_cons l_503000142153152042052 (sem_forall_cons l_503000142153152042053 (sem_forall_cons l_50300014215315204214 (sem_forall_cons l_503000142153152042152 (sem_forall_cons l_503000142153152042153 (sem_forall_cons l_50300014215315204304 (sem_forall_cons l_50300014215315204305 (sem_forall_cons l_50300014215315204314 (sem_forall_cons l_50300014215315204315 (sem_forall_cons l_503000142153152052024 (sem_forall_cons l_5030001421531520520250 (sem_forall_cons l_5030001421531520520251 (sem_forall_cons l_503000142153152052034 (sem_forall_cons l_503000142153152052035 (sem_forall_cons l_503000142153152052124 (sem_forall_cons l_5030001421531520521250 (sem_forall_cons l_5030001421531520521251 (sem_forall_cons l_503000142153152052134 (sem_forall_cons l_5030001421531520521350 (sem_forall_cons l_5030001421531520521351 (sem_forall_cons l_503000142153152053042 (sem_forall_cons l_503000142153152053043 (sem_forall_cons l_503000142153152053052 (sem_forall_cons l_503000142153152053053 (sem_forall_cons l_503000142153152053142 (sem_forall_cons l_503000142153152053143 (sem_forall_cons l_5030001421531520531520 (sem_forall_cons l_5030001421531520531521 (sem_forall_cons l_503000142153152053153 (sem_forall_cons l_50300014215315214204 (sem_forall_cons l_503000142153152142052 (sem_forall_cons l_503000142153152142053 (sem_forall_cons l_50300014215315214214 (sem_forall_cons l_503000142153152142152 (sem_forall_cons l_503000142153152142153 (sem_forall_cons l_50300014215315214304 (sem_forall_cons l_503000142153152143052 (sem_forall_cons l_503000142153152143053 (sem_forall_cons l_50300014215315214314 (sem_forall_cons l_503000142153152143152 (sem_forall_cons l_503000142153152143153 (sem_forall_cons l_503000142153152152024 (sem_forall_cons l_50300014215315215202502 (sem_forall_cons l_50300014215315215202503 (sem_forall_cons l_50300014215315215202512 (sem_forall_cons l_50300014215315215202513 (sem_forall_cons l_503000142153152152034 (sem_forall_cons l_5030001421531521520350 (sem_forall_cons l_50300014215315215203512 (sem_forall_cons l_50300014215315215203513 (sem_forall_cons l_5030001421531521521240 (sem_forall_cons l_5030001421531521521241 (sem_forall_cons l_50300014215315215212502 (sem_forall_cons l_50300014215315215212503 (sem_forall_cons l_50300014215315215212512 (sem_forall_cons l_50300014215315215212513 (sem_forall_cons l_503000142153152152134 (sem_forall_cons l_50300014215315215213502 (sem_forall_cons l_50300014215315215213503 (sem_forall_cons l_50300014215315215213512 (sem_forall_cons l_50300014215315215213513 (sem_forall_cons l_503000142153152153042 (sem_forall_cons l_503000142153152153043 (sem_forall_cons l_5030001421531521530520 (sem_forall_cons l_5030001421531521530521 (sem_forall_cons l_5030001421531521530530 (sem_forall_cons l_5030001421531521530531 (sem_forall_cons l_503000142153152153142 (sem_forall_cons l_503000142153152153143 (sem_forall_cons l_5030001421531521531520 (sem_forall_cons l_50300014215315215315212 (sem_forall_cons l_50300014215315215315213 (sem_forall_cons l_5030001421531521531530 (sem_forall_cons l_5030001421531521531531 (sem_forall_cons l_50300014215315304214 (sem_forall_cons l_50300014215315304215 (sem_forall_cons l_503000142153153052142 (sem_forall_cons l_503000142153153052143 (sem_forall_cons l_503000142153153052152 (sem_forall_cons l_503000142153153052153 sem_forall_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end P0132

namespace P0133

end P0133
end CKLaneM03.EP


