-- Prove2me | Definitions.Def_CK_CKLaneM10_Leaves_q00_q00
-- name    : CK_CKLaneM10_Leaves_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T22:51:33.468805+00:00
-- url     : https://prove2.me/theorems/8951c825-a967-4c0d-896c-54567df61085
-- title:
--   Courtade–Kumar proof module `CKLaneM10.Leaves (piece 1 of 3) (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM10.Leaves (piece 1 of 3) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM10.Leaves (piece 1 of 3) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM10.Leaves (piece 1 of 3) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM10/Leaves (piece 1 of 3) (piece 1 of 3).lean)

import Definitions.Def_CK_CKLaneD_ArchTree
import Definitions.Def_CK_CKLaneM10_Fleet_S0000__6
import Definitions.Def_CK_CKLaneM10_Fleet_S0006__7
import Definitions.Def_CK_CKLaneM10_Fleet_S0013__7
import Definitions.Def_CK_CKLaneM10_Fleet_S0020__7
import Definitions.Def_CK_CKLaneM10_Fleet_S0027__6
import Definitions.Def_CK_CKLaneM10_Fleet_S0033__7
import Definitions.Def_CK_CKLaneM10_Fleet_S0040__6
import Definitions.Def_CK_CKLaneM10_Fleet_S0046__5
import Definitions.Def_CK_CKLaneM10_Fleet_S0051__5
import Definitions.Def_CK_CKLaneM10_Fleet_S0056__5
import Definitions.Def_CK_CKLaneM10_Fleet_S0061__6
import Definitions.Def_CK_CKLaneM10_Fleet_S0067__4
import Definitions.Def_CK_CKLaneM10_Fleet_S0071__6
import Definitions.Def_CK_CKLaneM10_Fleet_S0077




/-!
# Lane M10: aggregate over ALL archived `global_feasible_split` leaves

`feasibleSplit_leaves_sem`: for every leaf `q` of Lane D's archived outer-opposite tree
(`CKLaneD.ArchTree.archTree`, label `3 = global_feasible_split`), the psi-candidate Bellman inequality
holds for every interior law in the FULL physical image `InUVT (uvtBox q.1)` of the leaf (no entropy
clipping).  Each shard proves its leaves by the Boolean checker `checkLeafFS` (`decide +kernel`) and
`checkLeafFS_sound`; `fsPaths_eq` identifies the shard paths with the archived label-3 paths.
-/

namespace CKLaneM10.Leaves

open CKLaneD CKLaneM10

theorem sem_append {L1 L2 : List (List ℕ × FSWitness)}
    (h1 : ∀ x ∈ L1, SemUVT (uvtBox x.1)) (h2 : ∀ x ∈ L2, SemUVT (uvtBox x.1)) :
    ∀ x ∈ L1 ++ L2, SemUVT (uvtBox x.1) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact h1 x h
  · exact h2 x h

end CKLaneM10.Leaves


