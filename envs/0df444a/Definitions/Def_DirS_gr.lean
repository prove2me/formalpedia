-- Prove2me | Definitions.Def_DirS_gr
-- name    : DirS_gr
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T18:08:26.375344+00:00
-- url     : https://prove2.me/theorems/40143336-13d9-4659-baf6-a362d283a73d
-- title:
--   The graph layer: oriented graphs, bipartite graphs, and their Sidorenko and forcing properties
-- statement:
--   The finite-graph layer of Fox, Himwich, Mani, and Zhou, "A note on directed analogues of the Sidorenko and forcing conjectures" (Electron. J. Combin. 32(3) (2025) #P3.38). OriGraph n is an oriented graph on Fin n: a Boolean edge relation with no loops (no_loop) and no two-cycles (no_two_cycle); OriGraph.und G is the underlying undirected adjacency; OriGraph.edgeCount G the number of (directed) edges; OriGraph.homCount B G the number of homomorphisms from B to G, the vertex maps carrying every edge of B to an edge of G; OriGraph.homDens B G the homomorphism density t(B,G) of Definition 1; OriGraph.dirDens G the directed edge density t(K_2, G) = e(G)/v(G)^2. DirSidorenko B is the directed Sidorenko property of Definition 3: for every oriented graph G, t(B,G) >= t(K_2, G)^{e(B)}. BipGraph m n is a bipartite graph between Fin m and Fin n, with BipGraph.bipEdgeCount, BipGraph.bipDens (the bipartite density |F|/|U_1||U_2|), BipGraph.bipHomCount (the part-respecting homomorphisms), and BipGraph.bipHomDens (the bipartite homomorphism density of Definition 10); AsymSidorenko A is the asymmetric Sidorenko property: t_bip(A,H) >= t_bip(K_2,H)^{e(A)} for all bipartite H. orientEdge and orientOf orient every edge of a bipartite graph from the first part to the second, on the disjoint sum of the two parts; knn n is the complete balanced bipartite orientation used in the paper's argument that directed Sidorenko forces a homomorphism to the edge. homToEdge B records a homomorphism to the directed edge K_2: a Boolean colouring whose edges go from false to true. hasCycle B records a cycle of length at least three in the underlying undirected graph, as an injective cyclic walk. DirForcing B is the directed forcing property of Definition 19 in a finitary epsilon-delta form; AsymForcing A is its asymmetric bipartite counterpart.
--
--   **Formalization Note** All vertex sets are Fin-indexed, so that all quantifications are over finite types without instance issues; the homomorphism conditions are Boolean list-membership tests over the fin-range lists; and the sequential forcing of Definition 19 is converted to the equivalent finitary epsilon-delta form, a conversion disclosed in the mission description.
-- source:
--   J. Fox, Z. Himwich, N. Mani, Y. Zhou, A note on directed analogues of the Sidorenko and forcing conjectures, Electron. J. Combin. 32(3) (2025) #P3.38, Sections 1-2 (Definitions 1, 3, 9, 10, and 19; Observation 20).

import Mathlib

/-!
# The graph layer: oriented graphs, bipartite graphs, and their Sidorenko and forcing properties

The graph layer of the DirS mission, carrying the finite-graph side of
Jacob Fox, Zoe Himwich, Nitya Mani, and Yunkun Zhou, "A note on directed
analogues of the Sidorenko and forcing conjectures" (Electron. J. Combin.
32(3) (2025) #P3.38): oriented graphs on Fin-indexed vertex sets as
loop-free, two-cycle-free Boolean edge relations; bipartite graphs between
Fin-indexed parts; the homomorphism counts and densities of Definitions 1,
3, and 10 of the paper; the directed and asymmetric Sidorenko properties;
the orientation of a bipartite graph and the complete balanced bipartite
orientation; the homomorphism-to-an-edge and underlying-cycle conditions;
and the directed and asymmetric forcing properties in a finitary
epsilon-delta form.
-/

namespace DirS

/-- An oriented graph on Fin n: a Boolean edge relation with no loops and
no two-cycles. -/
structure OriGraph (n : ℕ) where
  edge : Fin n → Fin n → Bool
  no_loop : ∀ x : Fin n, edge x x = false
  no_two_cycle : ∀ x y : Fin n, edge x y = true → edge y x = false

/-- The underlying undirected adjacency: an edge in either direction. -/
def OriGraph.und {n : ℕ} (G : OriGraph n) (x y : Fin n) : Bool :=
  G.edge x y || G.edge y x

/-- The number of (directed) edges of G. -/
def OriGraph.edgeCount {n : ℕ} (G : OriGraph n) : ℕ :=
  ((Finset.univ.product Finset.univ).filter (fun p => G.edge p.1 p.2)).card

/-- The number of homomorphisms from B to G: the vertex maps that carry
every edge of B to an edge of G. -/
def OriGraph.homCount {m n : ℕ} (B : OriGraph m) (G : OriGraph n) : ℕ :=
  ((Finset.univ : Finset (Fin m → Fin n)).filter
    (fun f => (List.finRange m).all
      (fun x => (List.finRange m).all
        (fun y => (!B.edge x y) || (G.edge (f x) (f y)))))).card

/-- The homomorphism density of B in G: the fraction of vertex maps that
are homomorphisms. -/
noncomputable def OriGraph.homDens {m n : ℕ} (B : OriGraph m) (G : OriGraph n) : ℝ :=
  (B.homCount G : ℝ) / ((n : ℝ) ^ (m : ℝ))

/-- The directed edge density of G: the fraction of ordered vertex pairs
that are edges. -/
noncomputable def OriGraph.dirDens {n : ℕ} (G : OriGraph n) : ℝ :=
  (G.edgeCount : ℝ) / ((n : ℝ) ^ (2 : ℝ))

/-- The directed Sidorenko property of Definition 3 of the paper: for every
oriented graph G, the homomorphism density of B is at least the directed
edge density of G to the power e(B). -/
def DirSidorenko {m : ℕ} (B : OriGraph m) : Prop :=
  ∀ (n : ℕ) (G : OriGraph n), (G.dirDens) ^ ((B.edgeCount : ℝ)) ≤ B.homDens G

/-- A bipartite graph between Fin m and Fin n: a Boolean adjacency
relation from the first part to the second. -/
structure BipGraph (m n : ℕ) where
  adj : Fin m → Fin n → Bool

/-- The number of edges of the bipartite graph A. -/
def BipGraph.bipEdgeCount {m n : ℕ} (A : BipGraph m n) : ℕ :=
  ((Finset.univ.product Finset.univ).filter (fun p => A.adj p.1 p.2)).card

/-- The bipartite edge density of H: the fraction of pairs between the
parts that are edges. -/
noncomputable def BipGraph.bipDens {m n : ℕ} (H : BipGraph m n) : ℝ :=
  (H.bipEdgeCount : ℝ) / ((m : ℝ) * (n : ℝ))

/-- The number of homomorphisms from A to H that respect the
bipartitions: the pairs of vertex maps sending the first part to the first
part and the second to the second that carry every edge of A to an edge
of H. -/
def BipGraph.bipHomCount {mA nA m n : ℕ} (A : BipGraph mA nA) (H : BipGraph m n) : ℕ :=
  ((Finset.univ : Finset ((Fin mA → Fin m) × (Fin nA → Fin n))).filter
    (fun f => (List.finRange mA).all
      (fun i => (List.finRange nA).all
        (fun j => (!A.adj i j) || (H.adj (f.1 i) (f.2 j)))))).card

/-- The bipartite homomorphism density of A in H: the fraction of
part-respecting pairs of vertex maps that are homomorphisms. -/
noncomputable def BipGraph.bipHomDens {mA nA m n : ℕ} (A : BipGraph mA nA) (H : BipGraph m n) : ℝ :=
  (A.bipHomCount H : ℝ) / (((m : ℝ) ^ (mA : ℝ)) * ((n : ℝ) ^ (nA : ℝ)))

/-- The asymmetric Sidorenko property of Definition 10 of the paper: for
every bipartite graph H, the bipartite homomorphism density of A is at
least the bipartite edge density of H to the power e(A). -/
def AsymSidorenko {mA nA : ℕ} (A : BipGraph mA nA) : Prop :=
  ∀ (m n : ℕ) (H : BipGraph m n), (H.bipDens) ^ ((A.bipEdgeCount : ℝ)) ≤ A.bipHomDens H

/-- The edge of the orientation of the bipartite graph H, on the vertex
set Fin (m + n): the i-th vertex of the left part maps to i, the j-th
vertex of the right part to m + j, and every edge is directed from the
left part to the right part. -/
def orientEdge (m n : ℕ) (H : BipGraph m n) (x y : Fin (m + n)) : Bool :=
  if h : x.val < m ∧ m ≤ y.val then
    H.adj (Fin.castLT x h.1) (⟨y.val - m, by have := y.isLt; omega⟩ : Fin n)
  else false

/-- The orientation of the bipartite graph H: the oriented graph on the
disjoint sum of the two parts with all edges directed from the first part
to the second. -/
def orientOf {m n : ℕ} (H : BipGraph m n) : OriGraph (m + n) where
  edge := orientEdge m n H
  no_loop := by
    intro x
    simp only [orientEdge]
    split
    · next h => exact absurd (Nat.lt_of_lt_of_le h.1 h.2) (Nat.lt_irrefl x.val)
    · rfl
  no_two_cycle := by
    intro x y hxy
    simp only [orientEdge] at hxy
    split at hxy
    · next h1 =>
      simp only [orientEdge]
      split
      · next h2 => exact absurd (Nat.lt_of_lt_of_le h1.1 h2.2) (Nat.lt_irrefl x.val)
      · rfl
    · exact Bool.noConfusion hxy

/-- The complete balanced bipartite orientation on n + n vertices, with all
edges directed from the first part to the second: the oriented graph
against which a graph without a homomorphism to the directed edge has no
copies. -/
def knn (n : ℕ) : OriGraph (n + n) :=
  orientOf (⟨fun _ _ => true⟩ : BipGraph n n)

/-- B has a homomorphism to the directed edge K_2: there is a Boolean
colouring of the vertices of B such that every edge goes from a
false-coloured vertex to a true-coloured vertex. -/
def homToEdge {m : ℕ} (B : OriGraph m) : Prop :=
  ∃ c : Fin m → Bool, ∀ x y : Fin m, B.edge x y = true → c x = false ∧ c y = true

/-- The underlying undirected graph of B has a cycle: there exist a length
k at least three and an injective cyclic sequence of vertices whose
consecutive steps are undirected edges. -/
def hasCycle {m : ℕ} (B : OriGraph m) : Prop :=
  ∃ (k : ℕ) (h3 : 3 ≤ k) (v : Fin k → Fin m),
    (∀ i j : Fin k, v i = v j → i = j) ∧
    ∀ i : Fin k,
      B.und (v i) (v ⟨(i.val + 1) % k,
        Nat.mod_lt (i.val + 1) (Nat.lt_of_lt_of_le (Nat.succ_pos 2) h3)⟩) = true

/-- The directed forcing property of Definition 19 of the paper, in a
finitary epsilon-delta form equivalent to the paper's sequential form: for
every density q in [0,1] and every positive epsilon there are a positive
delta and a threshold N such that every oriented graph G on at least N
vertices whose directed edge density is within delta of q and whose
B-density is within delta of the random value q ^ e(B) has, for every
oriented graph A, its A-density within epsilon of the random value
q ^ e(A). -/
def DirForcing {m : ℕ} (B : OriGraph m) : Prop :=
  ∀ q : ℝ, 0 ≤ q → q ≤ 1 → ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ G : OriGraph n,
      |G.dirDens - q| < δ → |B.homDens G - q ^ (B.edgeCount : ℝ)| < δ →
        ∀ (k : ℕ) (A : OriGraph k),
          |A.homDens G - q ^ (A.edgeCount : ℝ)| < ε

/-- The asymmetric forcing property of Definition 19 of the paper, in the
same finitary epsilon-delta form over bipartite graphs: for every density
q in [0,1] and every positive epsilon there are a positive delta and a
threshold N such that every bipartite graph H whose parts both have at
least N vertices, whose bipartite density is within delta of q, and whose
A-density is within delta of q ^ e(A) has, for every bipartite graph C,
its C-density within epsilon of q ^ e(C). -/
def AsymForcing {mA nA : ℕ} (A : BipGraph mA nA) : Prop :=
  ∀ q : ℝ, 0 ≤ q → q ≤ 1 → ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n → ∀ H : BipGraph m n,
      |H.bipDens - q| < δ → |A.bipHomDens H - q ^ (A.bipEdgeCount : ℝ)| < δ →
        ∀ (mC nC : ℕ) (C : BipGraph mC nC),
          |C.bipHomDens H - q ^ (C.bipEdgeCount : ℝ)| < ε

end DirS


