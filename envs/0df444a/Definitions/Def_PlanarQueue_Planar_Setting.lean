-- Prove2me | Definitions.Def_PlanarQueue_Planar_Setting
-- name    : PlanarQueue_Planar_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T13:23:47.00701+00:00
-- url     : https://prove2.me/theorems/69a6ef5a-6ac0-4a57-860c-05d9ac0fae1a
-- title:
--   Queue layouts, layerings, and graph partitions
-- statement:
--   A finite simple graph has a **queue layout** when its vertices have a linear order and its edges are assigned to queues so that no two edges in one queue nest. Edges nest when their four distinct endpoints occur in the order outer-left, inner-left, inner-right, outer-right. The graph has queue-number at most $k$ when it has such a layout with $k$ queues:
--
--   $$
--   \operatorname{qn}(G)\le k
--   \quad\Longleftrightarrow\quad
--   \exists\text{ a vertex order and a non-nesting assignment }E(G)\to [k].
--   $$
--
--   A **layering** assigns each vertex a nonnegative integer, with adjacent vertices in equal or consecutive layers. A **BFS layering** has one root in each connected component and assigns graph distance from that root. An **$H$-partition** assigns vertices of $G$ to vertices of $H$; an edge of $G$ either remains within one part or joins parts adjacent in $H$. The quotient graph has the nonempty parts as vertices and an edge whenever the original graph has an edge between two parts.
--
--   The planarity predicate is the published crossing-free plane-drawing definition, reused under a compatibility name for the paper's planar statements.
--
--   **Formalization Note** A queue assignment is defined only on actual edges, so an edgeless graph admits zero queues. The imported planarity and treewidth definitions use the same finite-simple-graph conventions as the paper.
-- source:
--   Dujmović, Joret, Micek, Morin, Ueckerdt, Wood, Planar graphs have bounded queue-number, arXiv:1904.04791v5, pp. 3–4, 7–9, §1–§2; plane graph p. 12

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace PlanarQueue.Planar

/-- Compatibility name for the published plane-drawing notion used by the paper. -/
abbrev IsPlanar {V : Type} (G : SimpleGraph V) : Prop :=
  RobertsonSeymour1986.GM5.IsPlanar G

/-- Two undirected edges nest in the given strict vertex order. -/
def Nested {V : Type} (ord : V → ℕ) (e f : Sym2 V) : Prop :=
  ∃ a b c d : V,
    ((e = s(a, d) ∧ f = s(b, c)) ∨ (e = s(b, c) ∧ f = s(a, d))) ∧
      ord a < ord b ∧ ord b < ord c ∧ ord c < ord d

/-- An injective order and a partition of the graph's edges into `k` queues. -/
def IsQueueLayout {V : Type} (G : SimpleGraph V) (k : ℕ)
    (ord : V → ℕ) (q : G.edgeSet → Fin k) : Prop :=
  Function.Injective ord ∧ ∀ e f : G.edgeSet, q e = q f → ¬ Nested ord e f

/-- The fixed vertex order admits a `k`-queue layout. -/
def OrderAdmits {V : Type} (G : SimpleGraph V) (k : ℕ) (ord : V → ℕ) : Prop :=
  ∃ q : G.edgeSet → Fin k, IsQueueLayout G k ord q

/-- The graph has a `k`-queue layout, equivalently queue-number at most `k`. -/
def HasQueueLayout {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ ord : V → ℕ, OrderAdmits G k ord

/-- The layer function labels adjacent vertices by equal or consecutive numbers. -/
def IsLayering {V : Type} (G : SimpleGraph V) (L : V → ℕ) : Prop :=
  ∀ v w, G.Adj v w → L v ≤ L w + 1 ∧ L w ≤ L v + 1

/-- One chosen root per connected component, and graph distance from that root. -/
def IsBFSLayering {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (L : V → ℕ) : Prop :=
  ∃ R : Finset V,
    (∀ v, ∃! r, r ∈ R ∧ G.Reachable r v) ∧
      ∀ r ∈ R, ∀ v, G.Reachable r v → L v = G.dist r v

/-- An `H`-indexed vertex partition: every edge stays within a part or crosses an edge of `H`. -/
def IsHPartition {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)
    (φ : V → W) : Prop :=
  ∀ v w, G.Adj v w → φ v = φ w ∨ H.Adj (φ v) (φ w)

/-- Quotient graph whose vertices are the nonempty parts of a partition. -/
def quotientGraph {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : Finpartition (Finset.univ : Finset V)) :
    SimpleGraph P.parts :=
  SimpleGraph.fromRel fun A B =>
    ∃ v ∈ A.1, ∃ w ∈ B.1, G.Adj v w

end PlanarQueue.Planar


