-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Traversals
-- name    : OAI_Combinatorics_HoneycombCorridor_Traversals
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:52:24.121391+00:00
-- url     : https://prove2.me/theorems/fde1c9e4-0388-4926-af9b-9896cb3f2eeb
-- title:
--   Traversals of honeycomb polygons and cycles at a vertex
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns.
--
--   1. **Closed walks are stopped.** A nonempty simple closed walk is stopped in the set of its own traced vertices.
--   2. **Traversals.** A polygon $P$ is traversed by $(g,w)$ if $w$ is a nonempty simple closed walk from $g$ whose word flow has support exactly the edges of $P$; then the vertex set of $P$ equals the set of traced vertices.
--   3. **Cycles at a vertex.** For a vertex $v$ of $P$, a cycle record $(k,w)$ at $v$ is a traversal of $P$ starting from the germ $(v,k)$:
--   $$
--   (k,w)\in\mathrm{cyclesAt}(P,v)\iff P\text{ is traversed by }((v,k),w).
--   $$
--   The finite set $\mathrm{cyclesAt}(P,v)$ collects all ways to go once around $P$ starting and ending at $v$, in either orientation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Traversals.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Traversals.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem closed_stopped (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g) :
    Stopped (traced g w).toFinset g w := by
  apply (stopped_iff_trace _ _ _).mpr
  refine ⟨hN,by simp,Or.inr ?_⟩
  rw [hc]
  obtain ⟨b,u,rfl⟩ := List.exists_cons_of_ne_nil hne
  simp [traced]

namespace Polygon

def Traverses (P : Polygon) (g : Germ) (w : List Bool) : Prop :=
  w ≠ [] ∧ (traced g w).Nodup ∧ terminalGerm g w = g ∧ (wordFlow g w).support = P.val

theorem Traverses.vertices {P : Polygon} {g : Germ} {w : List Bool}
    (h : P.Traverses g w) : P.vertices = (traced g w).toFinset := by
  change edgeVertices P.val = _
  rw [← h.2.2.2]
  exact wordFlow_edgeVertices g w h.2.1 h.2.2.1

end Polygon

def IsCycleAt (P : Polygon) (v : Vertex) (e : Fin 3 × List Bool) : Prop :=
  P.Traverses (v,e.1) e.2

noncomputable def cyclesAt (P : Polygon) (v : Vertex) : Finset (Fin 3 × List Bool) := by
  classical
  exact (Finset.univ.biUnion fun k : Fin 3 =>
    (leaves P.vertices (v,k)).image fun w => (k,w)).filter (IsCycleAt P v)

@[simp] theorem mem_cyclesAt (P : Polygon) (v : Vertex) (e : Fin 3 × List Bool) :
    e ∈ cyclesAt P v ↔ IsCycleAt P v e := by
  classical
  rw [cyclesAt,Finset.mem_filter]
  constructor
  · exact And.right
  · intro he
    refine ⟨Finset.mem_biUnion.mpr ⟨e.1,Finset.mem_univ _,Finset.mem_image.mpr
      ⟨e.2,?_,rfl⟩⟩,he⟩
    apply (mem_leaves_iff _ _ _).mpr
    rw [he.vertices]
    exact closed_stopped _ _ he.1 he.2.1 he.2.2.1

end PolynomialVacuumBridge.Corridor

end

end OAI


