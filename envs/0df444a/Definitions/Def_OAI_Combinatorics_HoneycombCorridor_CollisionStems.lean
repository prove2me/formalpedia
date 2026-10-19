-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionStems
-- name    : OAI_Combinatorics_HoneycombCorridor_CollisionStems
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:55:53.012849+00:00
-- url     : https://prove2.me/theorems/03c898bd-1ba5-4b3a-962e-95e753ea2c6f
-- title:
--   Stems attaching a ray to a polygon and ray collisions
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns. A ray record $s=(k,w)$ at $v$ describes the walk from $\mathrm{rayGerm}(v,k)$ (step from $v$ through slot $k$) following $w$.
--
--   1. **Stem end.** $\mathrm{stemEnd}(v,s)$ is the terminal germ of this walk.
--   2. **Polygon stems.** For a domain $D$, a vertex $v$ and a polygon $P$, $s$ is a polygon stem if $v$ is not on $P$, the walk is stopped in $(D\setminus P)\setminus\{v\}$, and it ends at a vertex of $P$. The finite set of such stems is $\mathrm{polygonStems}(D,v,P)$.
--   3. **Ray collisions.** $\mathrm{rayCollisions}(D,v)$ consists of the ray leaves whose stem end lies in $D\setminus\{v\}$:
--   $$
--   s\in\mathrm{rayCollisions}(D,v)\iff s\text{ is stopped in }D\setminus\{v\}\text{ and }\mathrm{stemEnd}(v,s)\in D\setminus\{v\},
--   $$
--   i.e. the walk ends by running into its own past instead of leaving $D$ or returning to $v$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/CollisionStems.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/CollisionStems.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def stemEnd (v : Vertex) (s : RayRecord) : Germ := terminalGerm (rayGerm v s.1) s.2

def IsPolygonStem (D : Finset Vertex) (v : Vertex) (P : Polygon) (s : RayRecord) : Prop :=
  v ∉ P.vertices ∧ Stopped ((D \ P.vertices).erase v) (rayGerm v s.1) s.2 ∧
    (stemEnd v s).1 ∈ P.vertices

noncomputable def polygonStems (D : Finset Vertex) (v : Vertex) (P : Polygon) :
    Finset RayRecord := by
  classical
  exact (rayLeaves (D \ P.vertices) v).filter (IsPolygonStem D v P)

@[simp] theorem mem_polygonStems (D : Finset Vertex) (v : Vertex) (P : Polygon) (s : RayRecord) :
    s ∈ polygonStems D v P ↔ IsPolygonStem D v P s := by
  classical
  simp only [polygonStems,Finset.mem_filter,mem_rayLeaves]
  exact ⟨And.right,fun h => ⟨h.2.1,h⟩⟩

noncomputable def rayCollisions (D : Finset Vertex) (v : Vertex) : Finset RayRecord := by
  classical
  exact (rayLeaves D v).filter fun e => (stemEnd v e).1 ∈ D.erase v

@[simp] theorem mem_rayCollisions (D : Finset Vertex) (v : Vertex) (e : RayRecord) :
    e ∈ rayCollisions D v ↔ Stopped (D.erase v) (rayGerm v e.1) e.2 ∧
      (stemEnd v e).1 ∈ D.erase v := by
  classical
  simp [rayCollisions]

end PolynomialVacuumBridge.Corridor

end

end OAI


