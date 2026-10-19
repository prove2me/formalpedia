-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryArcs
-- name    : OAI_Combinatorics_HoneycombCorridor_BoundaryArcs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T11:09:50.598068+00:00
-- url     : https://prove2.me/theorems/d6194034-73ea-4d32-bdea-1180cf714739
-- title:
--   Port identities for walks along a domain boundary
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns. The stem germ of $(g,b)$ is the germ at the same vertex whose slot is the unused outgoing slot of $(g,b)$.
--
--   1. Turn units are additive under concatenation: $\mathrm{turnUnits}(u\,w)=\mathrm{turnUnits}(u)+\mathrm{turnUnits}(w)$.
--   2. Reversing the stem of a right turn gives the left-turn successor, and conversely:
--   $$
--   \mathrm{reverseGerm}(\mathrm{stem}(g,\text{right}))=\mathrm{advance}(g,\text{left}),\qquad\mathrm{reverseGerm}(\mathrm{advance}(g,\text{left}))=\mathrm{stem}(g,\text{right}).
--   $$
--   3. **Ports.** At a vertex $v$, the stem of a right turn from $(v,k+1)$ is $(v,k)$, and a left turn from $(v,k+1)$ leads to $\mathrm{reverseGerm}(v,k)$. These identities connect consecutive boundary germs of a domain when walks are cut and glued along the boundary.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/BoundaryArcs.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/BoundaryArcs.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

@[simp] theorem turnUnits_append (u w : List Bool) :
    turnUnits (u ++ w) = turnUnits u + turnUnits w := by
  simp [turnUnits]

@[simp] theorem reverse_stem_false (g : Germ) :
    reverseGerm (stemGerm g false) = advance g true := rfl

@[simp] theorem reverse_advance_true (g : Germ) :
    reverseGerm (advance g true) = stemGerm g false := by
  rw [← reverse_stem_false,reverseGerm_reverseGerm]

@[simp] theorem boundary_stem_port (v : Vertex) (k : Fin 3) :
    stemGerm (v,k+1) false = (v,k) := by
  fin_cases k <;> simp [stemGerm,unusedSlot,outgoingSlot]

@[simp] theorem boundary_inward_port (v : Vertex) (k : Fin 3) :
    advance (v,k+1) true = reverseGerm (v,k) := by
  rw [← reverse_stem_false,boundary_stem_port]

end PolynomialVacuumBridge.Corridor

end

end OAI


