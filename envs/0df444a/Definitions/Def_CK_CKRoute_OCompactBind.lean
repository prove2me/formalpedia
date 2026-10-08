-- Prove2me | Definitions.Def_CK_CKRoute_OCompactBind
-- name    : CK_CKRoute_OCompactBind
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T23:52:13.741253+00:00
-- url     : https://prove2.me/theorems/6d52b9b5-32ee-441f-b2e4-0e72ef7d13e3
-- title:
--   Courtade–Kumar proof module `CKRoute.OCompactBind` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKRoute.OCompactBind` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKRoute.OCompactBind` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKRoute.OCompactBind (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKRoute/OCompactBind.lean)

import Definitions.Def_CK_CKRoute_Manuscript
import Definitions.Def_CK_CKLaneD_OCompact

-- ===== source module CKRoute.OCompactBind =====
section

/-!
# Binding Lane D's (O)-tree aggregation to the manuscript row `OP_Compact`

`CKLaneD.OCompact.OPCompactRow` is a verbatim copy of `CKRoute.OP_Compact`; the
equivalence below is definitional. The aggregation hypothesis ranges over all
29,495 leaves of the archived outer-opposite partition `CKLaneD.ArchTree.archTree`
(root `[3,28] × [1,28] × [0,1]` in `(u,v,t)`), each on its full archived image.
-/

namespace CKRoute

open GeneralCK

theorem opCompact_iff_laneD : OP_Compact ↔ CKLaneD.OCompact.OPCompactRow := Iff.rfl

/-- Conditional: the (O) row from per-leaf ownership of every archived leaf. -/
theorem opCompact_of_archLeaves
    (h : ∀ q ∈ CKLaneD.ArchTree.archTree.leaves,
      CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1)) :
    OP_Compact :=
  opCompact_iff_laneD.mpr (CKLaneD.OCompact.opCompact_of_leaves h)

end CKRoute

end


