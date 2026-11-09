-- Prove2me | Definitions.Def_WeakGraphOracles_OneSided_graphs
-- name    : WeakGraphOracles_OneSided_graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:18:31.44493+00:00
-- url     : https://prove2.me/theorems/4aff3866-0a43-4dbb-bbf4-c3ca8e4b73ae
-- title:
--   Forbidden patterns, deletion distance, and structured copy collections
-- statement:
--   A pattern $H$ is a finite simple graph on its own finite labeled vertex set. An eligible pattern is connected and has at least one edge. A family $F$ is admissible with bound $k$ when every member is eligible and has at most $k$ edges. An appearance is an injective adjacency-preserving map, so extra edges between its images are permitted. A graph is $F$-free when no member appears.
--
--   For an input graph $G$ on $n$ labels, define
--
--   $$d_F(G)=\min\{|D|:D\subseteq E(G),\;G-D\text{ is }F\text{-free}\}.$$
--
--   Edge farness is $d_F(G)>\epsilon|E(G)|$; vertex farness is $d_F(G)>\epsilon n$. The minimum is computed from deletion sets, rather than supplied as data. For admissible families it is attained and finite; for a free graph, including the empty family, it is zero. The extended nonnegative value is infinity if the feasible family is empty outside that domain.
--
--   An edge-disjoint collection consists of labeled appearances with disjoint edge images. It is role preserving if one map from the input vertices to $V(H)$ agrees with every inverse copy labeling. Its union graph uses exactly the supplied edge images. A vertex is heavy at threshold $h$ if its degree in $G$ is at least $h$; semi-bipartiteness means no edge joins two heavy vertices. These auxiliary notions impose no restriction on general inputs to the goal.
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 2 (PDF p. 3), §1.1; pp. 4–5 (PDF pp. 5–6), §3; pp. 6–8 (PDF pp. 7–9), §4.1, Definitions 2–5; p. 17 (PDF p. 18), §7.4

import Mathlib

set_option autoImplicit false

namespace WeakGraphOracles.OneSided

/-- A fixed finite forbidden pattern; the input graph need not be connected. -/
structure Pattern where
  order : ℕ
  graph : SimpleGraph (Fin order)

noncomputable def edges {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Sym2 (Fin n)) := by
  classical
  exact G.edgeFinset

/-- The standing assumptions of §§1.1 and 4.1. Positive edge count together
with connectedness excludes isolated vertices, including the singleton pattern. -/
def EligiblePattern (H : Pattern) : Prop :=
  H.graph.Connected ∧ 0 < (edges H.graph).card

def AdmissiblePattern (H : Pattern) (k : ℕ) : Prop :=
  EligiblePattern H ∧ (edges H.graph).card ≤ k

def AdmissibleFamily (F : Finset Pattern) (k : ℕ) : Prop :=
  ∀ H ∈ F, AdmissiblePattern H k

abbrev Appearance (H : Pattern) {n : ℕ} (G : SimpleGraph (Fin n)) :=
  SimpleGraph.Copy H.graph G

def Free {n : ℕ} (F : Finset Pattern) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ H ∈ F, IsEmpty (Appearance H G)

/-- Actual deletion sets on the same labeled vertex set. -/
def delete {n : ℕ} (G : SimpleGraph (Fin n)) (D : Finset (Sym2 (Fin n))) :
    SimpleGraph (Fin n) := G.deleteEdges (D : Set (Sym2 (Fin n)))

/-- Minimum deletion cardinality. On the finite set of feasible deletion sets,
this infimum is the attained minimum. No feasible set gives +infinity (only
possible for inadmissible patterns); empty families and free graphs give zero. -/
noncomputable def deletionDistance {n : ℕ} (F : Finset Pattern)
    (G : SimpleGraph (Fin n)) : ENNReal :=
  ⨅ (D : Finset (Sym2 (Fin n))) (_ : D ⊆ edges G) (_ : Free F (delete G D)),
    (D.card : ENNReal)

/-- Strict edge-normalized farness (§3), without division by the edge count. -/
def EdgeFar {n : ℕ} (F : Finset Pattern) (ε : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  ENNReal.ofReal (ε * (edges G).card) < deletionDistance F G

/-- Strict vertex-normalized farness in §7.4. -/
def VertexFar {n : ℕ} (F : Finset Pattern) (ε : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  ENNReal.ofReal (ε * n) < deletionDistance F G

noncomputable def copyEdges {n : ℕ} {H : Pattern} {G : SimpleGraph (Fin n)}
    (c : Appearance H G) : Finset (Sym2 (Fin n)) := by
  classical
  exact (edges G).filter fun e => ∃ a b, H.graph.Adj a b ∧ e = s(c a, c b)

def EdgeDisjoint {n : ℕ} {H : Pattern} {G : SimpleGraph (Fin n)}
    (C : Finset (Appearance H G)) : Prop :=
  ∀ c ∈ C, ∀ d ∈ C, c ≠ d → Disjoint (copyEdges c) (copyEdges d)

/-- One role assignment agrees with the inverse label of every supplied copy. -/
def RolePreserving {n : ℕ} {H : Pattern} {G : SimpleGraph (Fin n)}
    (C : Finset (Appearance H G)) : Prop :=
  ∃ ρ : Fin n → Fin H.order, ∀ c ∈ C, ∀ a, ρ (c a) = a

noncomputable def copyUnion {n : ℕ} {H : Pattern} {G : SimpleGraph (Fin n)}
    (C : Finset (Appearance H G)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | ∃ c ∈ C, e ∈ copyEdges c}

noncomputable def Heavy {n : ℕ} (G : SimpleGraph (Fin n)) (h : ℕ) (v : Fin n) : Prop :=
  h ≤ (G.neighborSet v).ncard

def SemiBipartite {n : ℕ} (G : SimpleGraph (Fin n)) (h : ℕ) : Prop :=
  ∀ u v, G.Adj u v → ¬ (Heavy G h u ∧ Heavy G h v)

end WeakGraphOracles.OneSided


