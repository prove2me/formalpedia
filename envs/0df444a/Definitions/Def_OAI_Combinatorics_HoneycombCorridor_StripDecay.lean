-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_StripDecay
-- name    : OAI_Combinatorics_HoneycombCorridor_StripDecay
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T11:28:56.695504+00:00
-- url     : https://prove2.me/theorems/b1912872-0445-4be5-9971-79f90f3094b1
-- title:
--   Walks lost by cutting a domain and the right index mass
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns. The bottom source is the germ $(\mathrm{up}(0,0),0)$, and $\mathrm{sourceExits}(D,g)$ is the set of stopped words from $g$ that leave $D$.
--
--   1. **Lost cut.** For a direction $k$ and an integer $A$, the lost cut consists of the source exits of $D$ that are not source exits of the cut domain $\mathrm{upperCut}(D,k,A)$:
--   $$
--   \mathrm{lostCut}(D,k,A)=\mathrm{sourceExits}(D,\mathrm{src})\setminus\mathrm{sourceExits}(\mathrm{upperCut}(D,k,A),\mathrm{src}).
--   $$
--   These are the walks that reach the region where the $k$-th box index is at least $A$.
--   2. **Right index mass.** $\mathrm{rightIndexMass}(D,A)$ is the positive mass $\sum\lambda^{|w|}$ of the lost cut in direction $k=1$, measuring walks that travel far to the right.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/StripDecay.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/StripDecay.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexCuts
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RaySeparation

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def lostCut (D : Finset Vertex) (k : Fin 3) (A : ℤ) : Finset (List Bool) :=
  sourceExits D bottomSource \ sourceExits (upperCut D k A) bottomSource

noncomputable def rightIndexMass (D : Finset Vertex) (A : ℤ) : ℝ :=
  positiveWordMass (lostCut D 1 A)

end PolynomialVacuumBridge.Corridor

end

end OAI


