-- Prove2me | Definitions.Def_CK_CKLaneM03_Family_F05_q00_q100
-- name    : CK_CKLaneM03_Family_F05_q00_q100
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T01:40:00.999486+00:00
-- url     : https://prove2.me/theorems/010cd52f-ba90-403b-9845-fc1bbf69014c
-- title:
--   Courtade–Kumar proof module `CKLaneM03.Family.F05 (piece 1 of 4) (piece 1 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM03.Family.F05 (piece 1 of 4) (piece 1 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM03.Family.F05 (piece 1 of 4) (piece 1 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM03.Family.F05 (piece 1 of 4) (piece 1 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM03/Family/F05 (piece 1 of 4) (piece 1 of 5).lean)

import Definitions.Def_CK_CKLaneM03_Family_F05_q00_q02


namespace CKLaneM03.EP
open CKLaneM03
namespace P0130
set_option maxRecDepth 200000 in
theorem leaves_sem : ∀ p ∈ leaves, Sem (ssBox p) :=
  sem_forall_cons l_50300014215212513503402 (sem_forall_cons l_50300014215212513503403 (sem_forall_cons l_50300014215212513503412 (sem_forall_cons l_50300014215212513503413 (sem_forall_cons l_503000142152125135035024 (sem_forall_cons l_50300014215212513503502502 (sem_forall_cons l_50300014215212513503502503 (sem_forall_cons l_50300014215212513503502512 (sem_forall_cons l_50300014215212513503502513 (sem_forall_cons l_503000142152125135035034 (sem_forall_cons l_5030001421521251350350350 (sem_forall_cons l_5030001421521251350350351 (sem_forall_cons l_5030001421521251350351240 (sem_forall_cons l_5030001421521251350351241 (sem_forall_cons l_50300014215212513503512502 (sem_forall_cons l_50300014215212513503512503 (sem_forall_cons l_50300014215212513503512512 (sem_forall_cons l_50300014215212513503512513 (sem_forall_cons l_503000142152125135035134 (sem_forall_cons l_50300014215212513503513502 (sem_forall_cons l_50300014215212513503513503 (sem_forall_cons l_50300014215212513503513512 (sem_forall_cons l_50300014215212513503513513 (sem_forall_cons l_503000142152125135124024 (sem_forall_cons l_503000142152125135124025 (sem_forall_cons l_503000142152125135124034 (sem_forall_cons l_503000142152125135124035 (sem_forall_cons l_503000142152125135124124 (sem_forall_cons l_5030001421521251351241250 (sem_forall_cons l_5030001421521251351241251 (sem_forall_cons l_503000142152125135124134 (sem_forall_cons l_503000142152125135124135 (sem_forall_cons l_50300014215212513512502402 (sem_forall_cons l_50300014215212513512502403 (sem_forall_cons l_50300014215212513512502412 (sem_forall_cons l_50300014215212513512502413 (sem_forall_cons l_5030001421521251351250340 (sem_forall_cons l_50300014215212513512503412 (sem_forall_cons l_50300014215212513512503413 (sem_forall_cons l_50300014215212513512503503 (sem_forall_cons l_50300014215212513512512402 (sem_forall_cons l_50300014215212513512512403 (sem_forall_cons l_50300014215212513512513402 (sem_forall_cons l_50300014215212513512513403 (sem_forall_cons l_50300014215212513512513412 (sem_forall_cons l_50300014215212513512513413 (sem_forall_cons l_50300014215212513513402 (sem_forall_cons l_50300014215212513513403 (sem_forall_cons l_503000142152125135134124 (sem_forall_cons l_503000142152125135134125 (sem_forall_cons l_50300014215212513513413 (sem_forall_cons l_5030001421521251351350240 (sem_forall_cons l_5030001421521251351350241 (sem_forall_cons l_50300014215212513513502502 (sem_forall_cons l_50300014215212513513502503 (sem_forall_cons l_50300014215212513513502512 (sem_forall_cons l_50300014215212513513502513 (sem_forall_cons l_503000142152125135135034 (sem_forall_cons l_50300014215212513513503502 (sem_forall_cons l_50300014215212513513503503 (sem_forall_cons l_50300014215212513513503512 (sem_forall_cons l_50300014215212513513503513 (sem_forall_cons l_5030001421521251351351240 (sem_forall_cons l_50300014215212513513512412 (sem_forall_cons l_50300014215212513513512413 (sem_forall_cons l_50300014215212513513512503 (sem_forall_cons l_5030001421521251351351340 (sem_forall_cons l_5030001421521251351351341 (sem_forall_cons l_50300014215212513513513502 (sem_forall_cons l_50300014215212513513513503 (sem_forall_cons l_50300014215212513513513512 (sem_forall_cons l_50300014215212513513513513 sem_forall_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end P0130

namespace P0131

end P0131
end CKLaneM03.EP


