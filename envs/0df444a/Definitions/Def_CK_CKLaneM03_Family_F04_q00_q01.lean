-- Prove2me | Definitions.Def_CK_CKLaneM03_Family_F04_q00_q01
-- name    : CK_CKLaneM03_Family_F04_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T06:57:04.573129+00:00
-- url     : https://prove2.me/theorems/cb17b7ae-d2c2-462e-9cf6-a0fa3f6d9f45
-- title:
--   Courtade–Kumar proof module `CKLaneM03.Family.F04 (piece 1 of 4) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM03.Family.F04 (piece 1 of 4) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM03.Family.F04 (piece 1 of 4) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM03.Family.F04 (piece 1 of 4) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM03/Family/F04 (piece 1 of 4) (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneM03_Family_F04_q00_q01_q03

namespace CKLaneM03.EP
open CKLaneM03
namespace P0104
set_option maxRecDepth 200000 in
theorem leaves_sem : ∀ p ∈ leaves, Sem (ssBox p) :=
  sem_forall_cons l_5020300143153051240240 (sem_forall_cons l_5020300143153051240241 (sem_forall_cons l_50203001431530512402502 (sem_forall_cons l_50203001431530512402503 (sem_forall_cons l_50203001431530512402512 (sem_forall_cons l_50203001431530512402513 (sem_forall_cons l_502030014315305124034 (sem_forall_cons l_50203001431530512403502 (sem_forall_cons l_50203001431530512403503 (sem_forall_cons l_50203001431530512403512 (sem_forall_cons l_50203001431530512403513 (sem_forall_cons l_5020300143153051241240 (sem_forall_cons l_50203001431530512412412 (sem_forall_cons l_50203001431530512412413 (sem_forall_cons l_50203001431530512412502 (sem_forall_cons l_50203001431530512412503 (sem_forall_cons l_502030014315305124125124 (sem_forall_cons l_502030014315305124125125 (sem_forall_cons l_50203001431530512412513 (sem_forall_cons l_5020300143153051241340 (sem_forall_cons l_5020300143153051241341 (sem_forall_cons l_50203001431530512413502 (sem_forall_cons l_50203001431530512413503 (sem_forall_cons l_50203001431530512413512 (sem_forall_cons l_50203001431530512413513 (sem_forall_cons l_5020300143153051250240240 (sem_forall_cons l_5020300143153051250240241 (sem_forall_cons l_50203001431530512502402502 (sem_forall_cons l_50203001431530512502402503 (sem_forall_cons l_50203001431530512502402512 (sem_forall_cons l_50203001431530512502402513 (sem_forall_cons l_502030014315305125024034 (sem_forall_cons l_50203001431530512502403502 (sem_forall_cons l_50203001431530512502403503 (sem_forall_cons l_50203001431530512502403512 (sem_forall_cons l_50203001431530512502403513 (sem_forall_cons l_5020300143153051250241240 (sem_forall_cons l_5020300143153051250241241 (sem_forall_cons l_50203001431530512502412502 (sem_forall_cons l_50203001431530512502412503 (sem_forall_cons l_50203001431530512502412512 (sem_forall_cons l_50203001431530512502412513 (sem_forall_cons l_502030014315305125024134 (sem_forall_cons l_50203001431530512502413502 (sem_forall_cons l_50203001431530512502413503 (sem_forall_cons l_50203001431530512502413512 (sem_forall_cons l_50203001431530512502413513 (sem_forall_cons l_50203001431530512502503403 (sem_forall_cons l_502030014315305125025034134 (sem_forall_cons l_502030014315305125034024 (sem_forall_cons l_5020300143153051250340250 (sem_forall_cons l_5020300143153051250340251 (sem_forall_cons l_502030014315305125034034 (sem_forall_cons l_5020300143153051250340350 (sem_forall_cons l_5020300143153051250340351 (sem_forall_cons l_502030014315305125034124 (sem_forall_cons l_50203001431530512503412502 (sem_forall_cons l_50203001431530512503412503 (sem_forall_cons l_50203001431530512503412512 (sem_forall_cons l_50203001431530512503412513 (sem_forall_cons l_502030014315305125034134 (sem_forall_cons l_5020300143153051250341350 (sem_forall_cons l_5020300143153051250341351 (sem_forall_cons l_50203001431530512503502402 (sem_forall_cons l_50203001431530512503502403 (sem_forall_cons l_50203001431530512503502412 (sem_forall_cons l_50203001431530512503502413 (sem_forall_cons l_50203001431530512503503402 (sem_forall_cons l_50203001431530512503503403 (sem_forall_cons l_50203001431530512503503412 (sem_forall_cons l_50203001431530512503503413 (sem_forall_cons l_502030014315305125035035024 (sem_forall_cons l_502030014315305125035035034 (sem_forall_cons l_502030014315305125035035134 (sem_forall_cons l_502030014315305125035124024 (sem_forall_cons l_50203001431530512503512403 (sem_forall_cons l_502030014315305125035124134 (sem_forall_cons l_50203001431530512503513402 (sem_forall_cons l_50203001431530512503513403 (sem_forall_cons l_50203001431530512503513412 (sem_forall_cons l_50203001431530512503513413 (sem_forall_cons l_502030014315305125035135034 (sem_forall_cons l_5020300143153051251240240 (sem_forall_cons l_50203001431530512512402412 (sem_forall_cons l_50203001431530512512402413 (sem_forall_cons l_50203001431530512512402502 (sem_forall_cons l_50203001431530512512402503 (sem_forall_cons l_50203001431530512512402513 (sem_forall_cons l_5020300143153051251240340 (sem_forall_cons l_5020300143153051251240341 (sem_forall_cons l_50203001431530512512403502 (sem_forall_cons l_50203001431530512512403503 (sem_forall_cons l_50203001431530512512403512 (sem_forall_cons l_50203001431530512512403513 (sem_forall_cons l_50203001431530512512412402 (sem_forall_cons l_50203001431530512512412403 (sem_forall_cons l_50203001431530512512412412 (sem_forall_cons l_50203001431530512512412413 (sem_forall_cons l_5020300143153051251241340 (sem_forall_cons l_50203001431530512512413412 (sem_forall_cons l_50203001431530512512413413 (sem_forall_cons l_50203001431530512512413502 (sem_forall_cons l_50203001431530512512413503 (sem_forall_cons l_50203001431530512512413513 sem_forall_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end P0104

namespace P0105

end P0105
end CKLaneM03.EP


