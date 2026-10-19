-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexDomains
-- name    : OAI_Combinatorics_HoneycombCorridor_ConvexDomains
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T11:13:29.134329+00:00
-- url     : https://prove2.me/theorems/742def58-e2ec-4dd1-baf0-d154ea0008a5
-- title:
--   Source exits and refined coordinate indices
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns.
--
--   1. **Source exits.** For a domain $D$ and a germ $g$, $\mathrm{sourceExits}(D,g)$ is the finite set of words $w$ that are stopped in $D$ from $g$ and whose final vertex lies outside $D$, i.e. self-avoiding walks from $g$ that leave $D$ without colliding with themselves.
--   2. **Coordinate index.** Each vertex receives three integer coordinates on a grid three times finer than the box indices:
--   $$
--   \mathrm{up}(i,j)\mapsto(3j+1,\ 3i+1,\ 3(i+j)+2),\qquad\mathrm{down}(i,j)\mapsto(3j+2,\ 3i+2,\ 3(i+j+1)+1).
--   $$
--   These separate up and down vertices in each direction and are proportional to the tiling coordinates of their positions, so linear inequalities in them describe convex domains.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/ConvexDomains.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/ConvexDomains.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def sourceExits (D : Finset Vertex) (g : Germ) : Finset (List Bool) := by
  classical
  exact (leaves D g).filter fun w => (terminalGerm g w).1 ∉ D

def coordinateIndex (v : Vertex) (k : Fin 3) : ℤ :=
  match v with
  | .up i j => if k = 0 then 3*j+1 else if k = 1 then 3*i+1 else 3*(i+j)+2
  | .down i j => if k = 0 then 3*j+2 else if k = 1 then 3*i+2 else 3*(i+j+1)+1

end PolynomialVacuumBridge.Corridor

end

end OAI


