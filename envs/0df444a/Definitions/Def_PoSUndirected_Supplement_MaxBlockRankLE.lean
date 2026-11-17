-- Prove2me | Definitions.Def_PoSUndirected_Supplement_MaxBlockRankLE
-- name    : PoSUndirected_Supplement_MaxBlockRankLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:30:01.174199+00:00
-- url     : https://prove2.me/theorems/750e6067-a4f7-42b4-a38a-85a3f4aa40fa
-- title:
--   Physical biconnected blocks, maximum block rank, theta graphs and subdivisions of $K_{3,3}$
-- statement:
--   For an edge set $A$, its incident vertices are $V(A)$. A physical block is a maximal vertex-biconnected edge set, with each bridge treated as a rank-zero singleton block. The assertion $b(G)\le r$ is written without truncated natural subtraction as
--   $$
--   |E(B)|+1\le |V(B)|+r
--   $$
--   for every physical block $B$; equality for some block gives maximum block rank exactly $r$.
--
--   A single theta is one physical block of cycle rank two with no isolated host vertices. A subdivision of $K_{3,3}$ is represented by six distinct branch vertices and nine pairwise edge-disjoint branch-to-branch paths whose internal vertices are mutually disjoint and avoid every branch vertex, and whose edges cover the physical host.
--
--   These definitions keep maximum physical block rank distinct from the total cycle rank of a disconnected or multi-block host.
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), §2, p.3 (PDF p.5); Theorems 4.2 and 4.4, pp.7–8 (PDF pp.9–10); Appendix B.10

import Mathlib
import Definitions.Def_PoSUndirected_Supplement_IsSocialOptimum

set_option autoImplicit false

namespace PoSUndirected.Supplement

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-!
# Physical blocks, block rank, theta graphs and subdivisions

Tsoufis, preprint sha256 c095d811…, §2, p.3 (PDF p.5), defines the cycle rank of a
connected edge set as `|A| - |V(A)| + 1`, counts a bridge as a rank-zero physical block, and
defines `b(G)` as the maximum rank of one physical biconnected block.
-/

/-- Connectivity of the subgraph carried by a nonempty edge set. -/
def IsConnectedEdgeSet (ends : E → Sym2 V) (A : Finset E) : Prop :=
  A.Nonempty ∧ ∀ u ∈ incidentVertices ends A, ∀ v ∈ incidentVertices ends A,
    ∃ P ⊆ A, IsSimplePathEdges ends u v P

/-- Vertex-biconnectivity of an edge set: it is connected and remains connected between every two
remaining incident vertices after any one incident vertex is deleted. -/
def IsVertexBiconnected (ends : E → Sym2 V) (A : Finset E) : Prop :=
  IsConnectedEdgeSet ends A ∧
    ∀ x ∈ incidentVertices ends A, ∀ u ∈ incidentVertices ends A, u ≠ x →
      ∀ v ∈ incidentVertices ends A, v ≠ x →
        ∃ P ⊆ A, IsSimplePathEdges ends u v P ∧ x ∉ incidentVertices ends P

/-- A physical biconnected block: a maximal vertex-biconnected edge set, with a singleton bridge
included as a block exactly when it is not contained in a larger biconnected edge set. -/
def IsPhysicalBlock (ends : E → Sym2 V) (B : Finset E) : Prop :=
  (B.card = 1 ∨ IsVertexBiconnected ends B) ∧
    ∀ A : Finset E, B ⊆ A → (A.card = 1 ∨ IsVertexBiconnected ends A) → A ⊆ B

/-- `b(G) ≤ r`, written without truncated natural subtraction: every physical block `B` obeys
`|E(B)| + 1 ≤ |V(B)| + r`, equivalently `β(B) ≤ r`. -/
def MaxBlockRankLE (ends : E → Sym2 V) (r : ℕ) : Prop :=
  ∀ B : Finset E, IsPhysicalBlock ends B →
    B.card + 1 ≤ (incidentVertices ends B).card + r

/-- The maximum physical block rank is exactly `r`. -/
def MaximumBlockRankEq (ends : E → Sym2 V) (r : ℕ) : Prop :=
  MaxBlockRankLE ends r ∧ ∃ B : Finset E, IsPhysicalBlock ends B ∧
    B.card + 1 = (incidentVertices ends B).card + r

/-- A single theta host: the whole physical graph is one block of cycle rank two.  For a finite
loopless multigraph this is precisely a subdivision of three parallel edges. -/
def IsSingleTheta (ends : E → Sym2 V) : Prop :=
  IsPhysicalBlock ends Finset.univ ∧
    Fintype.card E + 1 = (incidentVertices ends Finset.univ).card + 2 ∧
    incidentVertices ends Finset.univ = Finset.univ

/-- A concrete simple path witness, retaining its vertices as well as its edge set. -/
structure SubdivisionPath (ends : E → Sym2 V) (u v : V) where
  vertices : List V
  edges : List E
  walk : IsWalkVE ends vertices edges
  nodup_vertices : vertices.Nodup
  first_vertex : vertices.head? = some u
  last_vertex : vertices.getLast? = some v

namespace SubdivisionPath

/-- Edge set of a path witness. -/
def edgeSet {ends : E → Sym2 V} {u v : V} (P : SubdivisionPath ends u v) : Finset E :=
  P.edges.toFinset

/-- Vertex set of a path witness. -/
def vertexSet {ends : E → Sym2 V} {u v : V} (P : SubdivisionPath ends u v) : Finset V :=
  P.vertices.toFinset

/-- Internal vertices of a path witness. -/
def internalVertices {ends : E → Sym2 V} {u v : V} (P : SubdivisionPath ends u v) : Finset V :=
  P.vertexSet \ {u, v}

end SubdivisionPath

/-- The whole physical multigraph is a subdivision of `K₃,₃`: six distinct branch vertices and
nine internally vertex-disjoint, edge-disjoint branch-to-branch paths cover every physical edge. -/
def IsSubdivisionK33 (ends : E → Sym2 V) : Prop :=
  ∃ branch : Fin 2 → Fin 3 → V,
    Function.Injective (fun p : Fin 2 × Fin 3 ↦ branch p.1 p.2) ∧
    ∃ P : (i : Fin 3) → (j : Fin 3) → SubdivisionPath ends (branch 0 i) (branch 1 j),
      (∀ i j i' j', (i, j) ≠ (i', j') →
        Disjoint (P i j).edgeSet (P i' j').edgeSet ∧
        Disjoint (P i j).internalVertices (P i' j').internalVertices) ∧
      (∀ i j a b, branch a b ∉ (P i j).internalVertices) ∧
      (∀ e : E, ∃ i j, e ∈ (P i j).edgeSet) ∧
      incidentVertices ends Finset.univ = Finset.univ

end PoSUndirected.Supplement


