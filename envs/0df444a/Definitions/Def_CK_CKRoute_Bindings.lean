-- Prove2me | Definitions.Def_CK_CKRoute_Bindings
-- name    : CK_CKRoute_Bindings
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T05:03:40.664834+00:00
-- url     : https://prove2.me/theorems/3d5cc754-1a7f-4391-aa58-0a09cb731862
-- title:
--   Courtade–Kumar proof module `CKRoute.Bindings` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKRoute.Bindings` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKRoute.Bindings` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKRoute.Bindings (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKRoute/Bindings.lean)

import Definitions.Def_CK_CKRoute_OCompactBind
import Definitions.Def_CK_CKLaneD_Structural
import Definitions.Def_CK_CKLaneN23_OpBoundaryStrip

-- ===== source module CKRoute.Bindings =====
section

/-!
# Rows of the manuscript route bound to closed lane theorems

* `OP_Corner` and `OP_BoundaryStrip`: Lane N23 (verbatim row copies, definitional).
* (O) labels 5 (`outside`, 449 leaves) and 12 (`global_corner`, 1 leaf): Lane D
  (`CKLaneD.Structural`), in the `OLeafOK` form consumed by `opCompact_of_archLeaves`.

`RemainingRows` lists exactly what the route still needs.
-/

namespace CKRoute

open GeneralCK

theorem route_opCorner : OP_Corner := CKLaneN23.row_opCorner

theorem route_opBoundaryStrip : OP_BoundaryStrip := CKLaneN23.row_opBoundaryStrip

/-- (O) leaves: labels 5 and 12 are discharged; the rest is the remaining hypothesis. -/
theorem archLeaves_of_rest
    (h : ∀ q ∈ CKLaneD.ArchTree.archTree.leaves, q.2 ≠ 5 → q.2 ≠ 12 →
      CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1)) :
    ∀ q ∈ CKLaneD.ArchTree.archTree.leaves,
      CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1) := by
  intro q hq
  by_cases h5 : q.2 = 5
  · exact CKLaneD.Structural.outside_oLeafOK q hq h5
  by_cases h12 : q.2 = 12
  · exact CKLaneD.Structural.corner_oLeafOK q hq h12
  exact h q hq h5 h12

/-- Everything the scope-locked route still needs. -/
structure RemainingRows : Prop where
  theorem71 : Theorem71Components
  centralSquare : CentralSquare
  ssCompact : SS_Compact
  opCompactLeaves : ∀ q ∈ CKLaneD.ArchTree.archTree.leaves, q.2 ≠ 5 → q.2 ≠ 12 →
    CKLaneD.OCompact.OLeafOK (CKLaneD.uvtBox q.1)

theorem RemainingRows.toRoute (h : RemainingRows) : ManuscriptRoute where
  phiBranch := h.theorem71.phiBranch
  centralSquare := h.centralSquare
  ssSmallMean := row_ssSmallMean
  ssRatioTail := row_ssRatioTail
  ssCompact := h.ssCompact
  opBoundaryStrip := route_opBoundaryStrip
  opCorner := route_opCorner
  opLowEntropy := row_opLowEntropy
  opCompact := opCompact_of_archLeaves (archLeaves_of_rest h.opCompactLeaves)

/-- Conditional: General CK from the remaining rows of the manuscript route. -/
theorem generalCourtadeKumar_of_remainingRows (h : RemainingRows) : GeneralCourtadeKumar :=
  generalCourtadeKumar_of_manuscriptRoute h.toRoute

end CKRoute

end


