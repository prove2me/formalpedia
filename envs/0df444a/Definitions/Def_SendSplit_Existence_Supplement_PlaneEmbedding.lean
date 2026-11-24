-- Prove2me | Definitions.Def_SendSplit_Existence_Supplement_PlaneEmbedding
-- name    : SendSplit_Existence_Supplement_PlaneEmbedding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:45:43.95082+00:00
-- url     : https://prove2.me/theorems/6d1195bf-b305-49ad-9e4e-e7e5881bc356
-- title:
--   Section 4 — topological plane embeddings, complementary faces and demand face sets
-- statement:
--   A plane embedding assigns distinct points of the real plane to vertices and a simple continuous arc to each labelled edge. Arc interiors avoid every vertex and every other edge. The edge labels retain the two distinct arcs of an antiparallel pair. The underlying point set contains all vertices, including isolated ones. A face is a connected component of its complement; a representative point selects the component without imposing any boundary regularity.
--
--   For a real demand vector $r$, the face set of a face $F$ is
--   $$D_F=\{v:r_v\ne0,\ p(v)\in\overline F\}.$$
--   This supplies the geometric setting of Theorem 3, allowing repeated facial boundary vertices and edges.
--
--   **Formalization Note** The generic embedding takes arbitrary vertex and edge types with specified endpoint maps. Its specialization to the published network has nodes $\mathrm{Fin}\,n$ and labelled arcs in $A$. Complex coordinates represent the real plane. No straightness, convexity, biconnectivity or cost condition is imposed.
-- source:
--   Erickson, Monma and Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Mathematics of Operations Research 12(4) (1987), DOI 10.1287/moor.12.4.634, pp. 638, 645–646, Sections 2 and 4, definition of face set (PDF 6, 13–14)

import Mathlib
import Definitions.Def_SendSplit_Existence_Network

set_option autoImplicit false

namespace SendSplit.Existence.Supplement

/-- The real plane, represented by complex coordinates. -/
abbrev Plane := ℂ

/-- An actual embedding of an edge-labelled loopless graph. The endpoints are supplied
separately from the embedding, so antiparallel directed arcs remain different edges.
No polygonality, differentiability, or straight endpoint germs are required. -/
structure PlaneEmbedding {V E : Type} (tail head : E → V) where
  pos : V → Plane
  pos_injective : Function.Injective pos
  curve : E → unitInterval → Plane
  continuous_curve : ∀ e, Continuous (curve e)
  injective_curve : ∀ e, Function.Injective (curve e)
  start : ∀ e, curve e 0 = pos (tail e)
  finish : ∀ e, curve e 1 = pos (head e)
  avoids_vertices : ∀ e s v, curve e s = pos v → s = 0 ∨ s = 1
  disjoint_interiors : ∀ e f s t, e ≠ f → curve e s = curve f t →
    (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)

/-- The underlying point set, including isolated vertices. -/
def PlaneEmbedding.trace {V E : Type} {tail head : E → V}
    (P : PlaneEmbedding tail head) : Set Plane :=
  Set.range P.pos ∪ {z | ∃ e s, P.curve e s = z}

/-- Faces are actual connected components of the complement of the drawing.
The point is a representative, not an extra boundary regularity condition. -/
structure PlaneFace {V E : Type} {tail head : E → V} (P : PlaneEmbedding tail head) where
  point : Plane
  outside : point ∉ P.trace

/-- The open complementary region represented by a face. Different representatives
of the same component give the same region and the same face set. -/
def PlaneFace.region {V E : Type} {tail head : E → V} {P : PlaneEmbedding tail head}
    (F : PlaneFace P) : Set Plane :=
  connectedComponentIn P.traceᶜ F.point

variable {n : ℕ}

/-- The edge identities are the original ordered pairs in `G.A`. -/
abbrev Drawing (G : ArcGraph n) :=
  PlaneEmbedding (fun e : {p // p ∈ G.A} => e.val.1)
    (fun e : {p // p ∈ G.A} => e.val.2)

/-- Exactly the nonzero-demand vertices incident with the given face. Boundary
incidence uses closure of the complementary region, allowing repeated facial walks. -/
noncomputable def faceSet {G : ArcGraph n} (P : Drawing G) (r : Fin n → ℝ)
    (F : PlaneFace P) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v => r v ≠ 0 ∧ P.pos v ∈ closure F.region

end SendSplit.Existence.Supplement


