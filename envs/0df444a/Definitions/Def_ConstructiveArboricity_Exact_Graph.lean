-- Prove2me | Definitions.Def_ConstructiveArboricity_Exact_Graph
-- name    : ConstructiveArboricity_Exact_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:38:09.951199+00:00
-- url     : https://prove2.me/theorems/f8b428a2-1020-41e5-9cd0-5199189fef57
-- title:
--   Finite simple graph inputs, partitions, arboricity and orientations
-- statement:
--   A finite simple graph has vertices $0,\ldots,n-1$ and distinct edge identities $0,\ldots,m-1$. Each edge has two different endpoints, and no two identities denote the same unordered pair. All isolated vertices remain part of the graph.
--
--   A color assignment to every edge specifies a partition; each color class must be acyclic for a forest partition. Empty classes are allowed. The arboricity is the least feasible number of forest classes, including zero for an edgeless graph. Pseudoarboricity reuses the published maximum of the ceiling of induced-edge density over nonempty vertex sets. The published counting predicate for pseudoforests is reused; its equivalence to the component formulation is a separate open bridge statement.
--
--   An orientation chooses exactly one endpoint as the tail of each edge. A $k$-out orientation bounds every outgoing-edge count by $k$. The minimum of the feasible bounds defines the minimum maximum outdegree, including the empty graph. Cyclic connected components are counted once rather than by their different cycle traversals.
--
--   The sparse input is $n,m$ followed by the endpoints of every edge in its input order. The output is the color count followed by one color per input edge. These definitions separate the mathematical optimum from its computation.
-- source:
--   Gholami, Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani and Shahrezaei, Constructive Arboricity in Almost-Linear Time for Dense Graphs, STOC 2027 submission #1476 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1476.pdf, §2, pp.7–8

import Mathlib
import Definitions.Def_SparseDisc_pseudoarboricity
import Definitions.Def_MalleableSched_Pseudoforest

/-! Finite simple inputs and edge-indexed outputs for Gholami et al., STOC 2027
submission #1476, §2, pp.7–8. Isolated vertices and empty colors are implicit.
The order of the endpoint list is arbitrary; each undirected edge occurs once. -/
namespace ConstructiveArboricity.Exact

structure Graph where
  n : ℕ
  m : ℕ
  ends : Fin m → Fin n × Fin n
  noLoops : ∀ e, (ends e).1 ≠ (ends e).2
  simple : Function.Injective (fun e => s((ends e).1, (ends e).2))

def Graph.edge (G : Graph) (e : Fin G.m) : Sym2 (Fin G.n) :=
  s((G.ends e).1, (G.ends e).2)

def Graph.onEdges (G : Graph) (S : Set (Fin G.m)) : SimpleGraph (Fin G.n) :=
  SimpleGraph.fromEdgeSet (G.edge '' S)

def Graph.graph (G : Graph) : SimpleGraph (Fin G.n) := G.onEdges Set.univ

def Graph.IsForest (G : Graph) (S : Set (Fin G.m)) : Prop :=
  (G.onEdges S).IsAcyclic

noncomputable def Graph.IsPseudoforest (G : Graph) (S : Set (Fin G.m)) : Prop := by
  classical
  exact MalleableSched.IsPseudoforestGraph (G.onEdges S)

def Graph.ForestPartition (G : Graph) (k : ℕ) (c : Fin G.m → Fin k) : Prop :=
  ∀ i, G.IsForest {e | c e = i}

def Graph.PseudoforestPartition (G : Graph) (k : ℕ) (c : Fin G.m → Fin k) : Prop :=
  ∀ i, G.IsPseudoforest {e | c e = i}

def Graph.Feasible (G : Graph) (k : ℕ) : Prop := ∃ c, G.ForestPartition k c

/-- Minimum feasible color count, with the natural infimum convention. The defining
set is nonempty for every `Graph`: assign a distinct color to each edge. -/
noncomputable def Graph.arboricity (G : Graph) : ℕ := sInf {k | G.Feasible k}

noncomputable def Graph.rho (G : Graph) : ℕ := SparseDisc.pseudoarboricity G.graph

def Graph.IsOrientation (G : Graph) (tail : Fin G.m → Fin G.n) : Prop :=
  ∀ e, tail e = (G.ends e).1 ∨ tail e = (G.ends e).2

def Graph.head (G : Graph) (tail : Fin G.m → Fin G.n) (e : Fin G.m) : Fin G.n :=
  if tail e = (G.ends e).1 then (G.ends e).2 else (G.ends e).1

noncomputable def Graph.outdegree (G : Graph) (tail : Fin G.m → Fin G.n)
    (v : Fin G.n) : ℕ := by
  classical
  exact (Finset.univ.filter fun e => tail e = v).card

def Graph.IsKOut (G : Graph) (k : ℕ) (tail : Fin G.m → Fin G.n) : Prop :=
  G.IsOrientation tail ∧ ∀ v, G.outdegree tail v ≤ k

noncomputable def Graph.minOutdegree (G : Graph) : ℕ :=
  sInf {k | ∃ tail, G.IsKOut k tail}

def Graph.edgesIn (G : Graph) (X : Set (Fin G.n)) : Set (Fin G.m) :=
  {e | (G.ends e).1 ∈ X ∧ (G.ends e).2 ∈ X}

/-- Cyclic connected components, each counted once, irrespective of walk representation. -/
noncomputable def Graph.cycleCount (G : Graph) (S : Set (Fin G.m)) : ℕ :=
  Nat.card {C : (G.onEdges S).ConnectedComponent //
    ∃ (v : Fin G.n) (p : (G.onEdges S).Walk v v), p.IsCycle ∧ v ∈ C.supp}

/-- Component form of the pseudoforest definition: each connected component loses
all its cycles after deleting at most one edge. This is equivalent to at most one cycle. -/
def Graph.ComponentPseudoforest (G : Graph) (S : Set (Fin G.m)) : Prop :=
  ∀ C : (G.onEdges S).ConnectedComponent,
    ∃ R : Finset (Fin G.m), R.card ≤ 1 ∧ (↑R : Set (Fin G.m)) ⊆ S ∩ G.edgesIn C.supp ∧
      G.IsForest ((S ∩ G.edgesIn C.supp) \ ↑R)

def Graph.input (G : Graph) : List ℤ :=
  [G.n, G.m] ++ (List.ofFn fun e : Fin G.m =>
    [(G.ends e).1.val, (G.ends e).2.val]).flatten

def Graph.partitionOutput (G : Graph) (k : ℕ) (c : Fin G.m → Fin k) : List ℤ :=
  (k : ℤ) :: List.ofFn (fun e => (c e).val)

end ConstructiveArboricity.Exact


