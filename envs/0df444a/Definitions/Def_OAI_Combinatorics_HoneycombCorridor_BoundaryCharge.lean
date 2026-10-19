-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryCharge
-- name    : OAI_Combinatorics_HoneycombCorridor_BoundaryCharge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T11:07:51.528996+00:00
-- url     : https://prove2.me/theorems/6cdeeb8a-9a22-439c-bdc3-079b71673d35
-- title:
--   Boundary charge of a face-boundary germ
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns. For a finite set $S$ of faces, a face-boundary germ $g$ has its left face outside $S$ and its right face inside $S$, and the boundary-following walk turns left at $g$ unless the face to the left of slot $g_2+1$ belongs to $S$.
--
--   1. The boundary turn at $g$ is a right turn exactly when $\mathrm{leftFace}(g_1,g_2+1)\in S$.
--   2. The boundary charge of a face-boundary germ is
--   $$
--   \mathrm{boundaryCharge}(S,g)=\begin{cases}0,&\text{the boundary walk turns left at }g,\\1,&\text{it turns right.}\end{cases}
--   $$
--   Summing charges along the boundary counts the right turns, which is used to relate turning numbers of boundary loops to the size of $S$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/BoundaryCharge.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/BoundaryCharge.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

@[simp] theorem faceBoundaryTurn_false (S : Finset FaceIndex) (g : Germ) :
    faceBoundaryTurn S g = false ↔ leftFace (g.1,g.2+1) ∈ S := by
  classical
  simp [faceBoundaryTurn]

noncomputable def boundaryCharge (S : Finset FaceIndex) (g : FaceBoundary S) : ℤ :=
  if faceBoundaryTurn S g.val then 0 else 1

end PolynomialVacuumBridge.Corridor

end

end OAI


