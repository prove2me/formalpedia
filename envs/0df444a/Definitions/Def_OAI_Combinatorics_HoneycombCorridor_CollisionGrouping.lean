-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionGrouping
-- name    : OAI_Combinatorics_HoneycombCorridor_CollisionGrouping
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:59:18.275114+00:00
-- url     : https://prove2.me/theorems/ba880d0e-7ba0-40b8-8a18-a4fc914ba61a
-- title:
--   Collision data: polygons with stems and cycles
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns. Collisions of walks started at a vertex $v$ of a domain $D$ are grouped by the loop they create.
--
--   The finite set $\mathrm{collisionData}(D,v)$ consists of triples $(P,s,c)$ where $P$ is a polygon of $D$, $s$ is a polygon stem from $v$ to $P$, and $c$ is a cycle around $P$ starting at the stem end:
--   $$
--   (P,s,c)\in\mathrm{collisionData}(D,v)\iff P\in\mathrm{polygons}(D),\ s\in\mathrm{polygonStems}(D,v,P),\ c\in\mathrm{cyclesAt}(P,\mathrm{stemEnd}(v,s)).
--   $$
--   A colliding walk is thereby decomposed into a self-avoiding stem from $v$ to the polygon and one traversal of the polygon, which is the basis for cancelling collision contributions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/CollisionGrouping.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/CollisionGrouping.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def collisionData (D : Finset Vertex) (v : Vertex) : Finset (Polygon × RayRecord × RayRecord) := by
  classical
  exact (polygons D).biUnion fun P =>
    ((polygonStems D v P).biUnion fun s =>
      (cyclesAt P (stemEnd v s).1).image fun c => (s,c)).image fun sc => (P,sc)

@[simp] theorem mem_collisionData (D : Finset Vertex) (v : Vertex) (P : Polygon) (s c : RayRecord) :
    (P,s,c) ∈ collisionData D v ↔ P ∈ polygons D ∧ s ∈ polygonStems D v P ∧
      c ∈ cyclesAt P (stemEnd v s).1 := by
  classical
  simp only [collisionData,Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨Q,hQ,⟨t,d⟩,⟨z,hz,a,ha,hza⟩,hQz⟩
    have he := Prod.mk.inj hQz
    have he' := Prod.mk.inj hza
    rcases he with ⟨rfl,he⟩
    have hzs : z = s := he'.1.trans (congrArg Prod.fst he)
    have hac : a = c := he'.2.trans (congrArg Prod.snd he)
    subst z
    subst a
    exact ⟨hQ,hz,ha⟩
  · rintro ⟨hP,hs,hc⟩
    exact ⟨P,hP,(s,c),⟨s,hs,c,hc,rfl⟩,rfl⟩

end PolynomialVacuumBridge.Corridor

end

end OAI


