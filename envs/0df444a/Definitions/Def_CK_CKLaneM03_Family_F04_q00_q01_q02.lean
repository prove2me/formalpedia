-- Prove2me | Definitions.Def_CK_CKLaneM03_Family_F04_q00_q01_q02
-- name    : CK_CKLaneM03_Family_F04_q00_q01_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T06:44:27.182168+00:00
-- url     : https://prove2.me/theorems/8d0b3bca-19fc-4213-ae2a-ed73b372dc24
-- title:
--   Courtade–Kumar proof module `CKLaneM03.Family.F04 (piece 1 of 4) (piece 2 of 4) (piece 3 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM03.Family.F04 (piece 1 of 4) (piece 2 of 4) (piece 3 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM03.Family.F04 (piece 1 of 4) (piece 2 of 4) (piece 3 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM03.Family.F04 (piece 1 of 4) (piece 2 of 4) (piece 3 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM03/Family/F04 (piece 1 of 4) (piece 2 of 4) (piece 3 of 5).lean)

import Definitions.Def_CK_CKLaneM03_Family_F04_q00_q01_q101

namespace CKLaneM03.EP
open CKLaneM03
namespace P0103
set_option maxRecDepth 200000 in
theorem leaves_sem : ∀ p ∈ leaves, Sem (ssBox p) :=
  sem_forall_cons l_502030014315305025135135024 (sem_forall_cons l_502030014315305025135135025 (sem_forall_cons l_502030014315305025135135034 (sem_forall_cons l_502030014315305025135135035 (sem_forall_cons l_502030014315305025135135124 (sem_forall_cons l_502030014315305025135135134 (sem_forall_cons l_502030014315305025135135135 (sem_forall_cons l_502030014315305034024 (sem_forall_cons l_5020300143153050340250 (sem_forall_cons l_5020300143153050340251 (sem_forall_cons l_502030014315305034034 (sem_forall_cons l_502030014315305034035 (sem_forall_cons l_502030014315305034124 (sem_forall_cons l_5020300143153050341250 (sem_forall_cons l_5020300143153050341251 (sem_forall_cons l_502030014315305034134 (sem_forall_cons l_5020300143153050341350 (sem_forall_cons l_5020300143153050341351 (sem_forall_cons l_50203001431530503502402 (sem_forall_cons l_50203001431530503502403 (sem_forall_cons l_50203001431530503502412 (sem_forall_cons l_50203001431530503502413 (sem_forall_cons l_502030014315305035025024 (sem_forall_cons l_50203001431530503502502502 (sem_forall_cons l_50203001431530503502502503 (sem_forall_cons l_50203001431530503502502512 (sem_forall_cons l_50203001431530503502502513 (sem_forall_cons l_502030014315305035025034 (sem_forall_cons l_5020300143153050350250350 (sem_forall_cons l_5020300143153050350250351 (sem_forall_cons l_502030014315305035025124 (sem_forall_cons l_50203001431530503502512502 (sem_forall_cons l_50203001431530503502512503 (sem_forall_cons l_50203001431530503502512512 (sem_forall_cons l_50203001431530503502512513 (sem_forall_cons l_502030014315305035025134 (sem_forall_cons l_5020300143153050350251350 (sem_forall_cons l_50203001431530503502513512 (sem_forall_cons l_50203001431530503502513513 (sem_forall_cons l_50203001431530503503402 (sem_forall_cons l_50203001431530503503403 (sem_forall_cons l_50203001431530503503412 (sem_forall_cons l_50203001431530503503413 (sem_forall_cons l_502030014315305035035024 (sem_forall_cons l_502030014315305035035025 (sem_forall_cons l_502030014315305035035034 (sem_forall_cons l_502030014315305035035035 (sem_forall_cons l_502030014315305035035124 (sem_forall_cons l_5020300143153050350351250 (sem_forall_cons l_5020300143153050350351251 (sem_forall_cons l_502030014315305035035134 (sem_forall_cons l_502030014315305035035135 (sem_forall_cons l_50203001431530503512402 (sem_forall_cons l_50203001431530503512403 (sem_forall_cons l_50203001431530503512412 (sem_forall_cons l_50203001431530503512413 (sem_forall_cons l_5020300143153050351250240 (sem_forall_cons l_5020300143153050351250241 (sem_forall_cons l_50203001431530503512502502 (sem_forall_cons l_50203001431530503512502503 (sem_forall_cons l_50203001431530503512502512 (sem_forall_cons l_50203001431530503512502513 (sem_forall_cons l_502030014315305035125034 (sem_forall_cons l_50203001431530503512503502 (sem_forall_cons l_50203001431530503512503503 (sem_forall_cons l_50203001431530503512503512 (sem_forall_cons l_50203001431530503512503513 (sem_forall_cons l_5020300143153050351251240 (sem_forall_cons l_5020300143153050351251241 (sem_forall_cons l_50203001431530503512512502 (sem_forall_cons l_50203001431530503512512503 (sem_forall_cons l_50203001431530503512512512 (sem_forall_cons l_50203001431530503512512513 (sem_forall_cons l_5020300143153050351251340 (sem_forall_cons l_5020300143153050351251341 (sem_forall_cons l_50203001431530503512513502 (sem_forall_cons l_50203001431530503512513503 (sem_forall_cons l_50203001431530503512513512 (sem_forall_cons l_50203001431530503512513513 (sem_forall_cons l_50203001431530503513402 (sem_forall_cons l_50203001431530503513403 (sem_forall_cons l_50203001431530503513412 (sem_forall_cons l_50203001431530503513413 (sem_forall_cons l_502030014315305035135024 (sem_forall_cons l_5020300143153050351350250 (sem_forall_cons l_50203001431530503513502512 (sem_forall_cons l_50203001431530503513502513 (sem_forall_cons l_502030014315305035135034 (sem_forall_cons l_5020300143153050351350350 (sem_forall_cons l_5020300143153050351350351 (sem_forall_cons l_502030014315305035135124 (sem_forall_cons l_50203001431530503513512502 (sem_forall_cons l_50203001431530503513512503 (sem_forall_cons l_50203001431530503513512512 (sem_forall_cons l_50203001431530503513512513 (sem_forall_cons l_502030014315305035135134 (sem_forall_cons l_5020300143153050351351350 (sem_forall_cons l_5020300143153050351351351 sem_forall_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end P0103

namespace P0104

end P0104
end CKLaneM03.EP


