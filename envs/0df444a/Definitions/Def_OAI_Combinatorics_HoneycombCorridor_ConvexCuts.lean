-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexCuts
-- name    : OAI_Combinatorics_HoneycombCorridor_ConvexCuts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T11:23:17.177985+00:00
-- url     : https://prove2.me/theorems/627e123b-f08e-4933-b41d-4f0f202c0197
-- title:
--   Half-plane cuts of a honeycomb domain
-- statement:
--   Each honeycomb vertex has three integer box indices $\mathrm{boxIndex}(v)_k$, $k\in\{0,1,2\}$, one per lattice direction (index $0$ is the layer).
--
--   For a finite vertex set $D$, a direction $k$ and an integer $A$, the upper cut keeps the vertices of $D$ whose $k$-th index is below $A$:
--   $$
--   \mathrm{upperCut}(D,k,A)=\{v\in D:\mathrm{boxIndex}(v)_k<A\}.
--   $$
--   Cutting an admissibly convex domain by such a half-plane gives again a convex domain. Comparing walks in $D$ with walks in its cuts isolates the contribution of walks that reach index $A$ in direction $k$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/ConvexCuts.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/ConvexCuts.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HoneycombBridgeFiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Incidence
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Curvature
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Polygons
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionPhase
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CycleSplice
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionHistories
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PolygonGeometry
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionCancellation
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Traversals
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ReturnCycles
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionStems
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionGrouping
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Convexity
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_FaceBoundary
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryCharge
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryContainment
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryArcs
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexDomains
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_VisitRecursion
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryFlux

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def upperCut (D : Finset Vertex) (k : Fin 3) (A : ℤ) : Finset Vertex :=
  D.filter fun v => boxIndex v k < A

@[simp] theorem mem_upperCut (D : Finset Vertex) (k : Fin 3) (A : ℤ) (v : Vertex) :
    v ∈ upperCut D k A ↔ v ∈ D ∧ boxIndex v k < A := by
  simp [upperCut]

end PolynomialVacuumBridge.Corridor

end

end OAI


