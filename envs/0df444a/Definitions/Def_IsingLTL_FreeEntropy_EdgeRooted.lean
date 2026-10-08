-- Prove2me | Definitions.Def_IsingLTL_FreeEntropy_EdgeRooted
-- name    : IsingLTL_FreeEntropy_EdgeRooted
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:13:33.429135+00:00
-- url     : https://prove2.me/theorems/b81e9f84-34ac-4f06-948d-5c1108a5e8db
-- title:
--   Edge balls $B_{ij}(t)$ and the edge-rooted tree $\bar T(\rho,t)$ (Lemma 6.4)
-- statement:
--   For an edge $(i,j)$ of a graph $G_n$ and $t\ge0$, $B_{ij}(t)$ is the subgraph of $G_n$ induced by the vertices at distance at most $t$ from $(i,j)$ (that is, from $i$ or from $j$), rooted at the edge $(i,j)$.
--
--   The tree $\bar T(\rho,\infty)$ is obtained by "gluing" two independent trees from the ensemble $T(\rho,\infty)$ through an extra edge $e$ between their roots, and considering $e$ as the root; $\bar T(\rho,t)$ is the subtree formed by its first $t$ generations, consisting of $e$ and two independent copies of $T(\rho,t)$.
--
--   **Formalization Note** The two copies are tagged `false` and `true`; the vertices of $\bar T(t)$ are the pairs (copy, word) with the word in the first $t$ generations of that copy, and the root edge joins the two empty words. $\bar T(\rho,t)$ is obtained when the two offspring functions are independent with law $T(\rho,\infty)$.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, pp. 24-25 (definition of $\bar T(\rho,\infty)$); p. 25, Lemma 6.4

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_LocalConvergence

namespace IsingLTL.FreeEntropy

/-- The vertex set of `B_ij(t)` (Dembo–Montanari, *Ising Models on Locally Tree-Like Graphs*,
arXiv:0804.4726v3, Lemma 6.4, p. 25): the vertices at distance at most `t` from the edge
`(i, j)`, i.e. at distance at most `t` from `i` or from `j`. -/
noncomputable def edgeBallSet {V : Type*} [Fintype V] (G : SimpleGraph V) (i j : V) (t : ℕ) :
    Finset V := by
  classical
  exact Finset.univ.filter (fun v => G.edist i v ≤ t ∨ G.edist j v ≤ t)

theorem left_mem_edgeBallSet {V : Type*} [Fintype V] (G : SimpleGraph V) (i j : V) (t : ℕ) :
    i ∈ (edgeBallSet G i j t : Set V) := by
  classical
  simp [edgeBallSet]

theorem right_mem_edgeBallSet {V : Type*} [Fintype V] (G : SimpleGraph V) (i j : V) (t : ℕ) :
    j ∈ (edgeBallSet G i j t : Set V) := by
  classical
  simp [edgeBallSet]

/-- The subgraph `B_ij(t)` of `G` induced by the vertices at distance at most `t` from the edge
`(i, j)` (Lemma 6.4, p. 25), rooted at the edge `{i, j}` (`edgeBallLeft`, `edgeBallRight`). -/
abbrev edgeBallGraph {V : Type*} [Fintype V] (G : SimpleGraph V) (i j : V) (t : ℕ) :=
  G.induce (edgeBallSet G i j t : Set V)

/-- The endpoint `i` of the root edge of `B_ij(t)`. -/
def edgeBallLeft {V : Type*} [Fintype V] (G : SimpleGraph V) (i j : V) (t : ℕ) :
    (edgeBallSet G i j t : Set V) :=
  ⟨i, left_mem_edgeBallSet G i j t⟩

/-- The endpoint `j` of the root edge of `B_ij(t)`. -/
def edgeBallRight {V : Type*} [Fintype V] (G : SimpleGraph V) (i j : V) (t : ℕ) :
    (edgeBallSet G i j t : Set V) :=
  ⟨j, right_mem_edgeBallSet G i j t⟩

/-- The graph of two disjoint copies of the Ulam–Harris word tree (copy `false` and copy
`true`), joined by an extra edge `e` between their roots `(false, [])` and `(true, [])`
(p. 24–25: the tree `T̄(ρ, ∞)` is obtained by "gluing" two trees through an edge between their
roots). -/
def edgeTreeGraph : SimpleGraph (Bool × List ℕ) :=
  SimpleGraph.fromRel (fun p q => (p.1 = q.1 ∧ treeGraph.Adj p.2 q.2) ∨
    (p.1 = false ∧ q.1 = true ∧ p.2 = [] ∧ q.2 = []))

/-- The vertices of `T̄(t)` (p. 24–25) built from the offspring functions `ω₁` (copy `false`)
and `ω₂` (copy `true`): the root edge `e` and the first `t` generations of each of the two trees
hanging from its endpoints. When `(ω₁, ω₂)` has law `rhoTree ⊗ rhoTree`, the subgraph of
`edgeTreeGraph` induced on this set, rooted at the edge `{(false, []), (true, [])}`, is
`T̄(ρ, t)`. -/
def edgeTreeSet (ω₁ ω₂ : List ℕ → ℕ) (t : ℕ) : Finset (Bool × List ℕ) :=
  (ballTree ω₁ t).image (Prod.mk false) ∪ (ballTree ω₂ t).image (Prod.mk true)

theorem false_nil_mem_edgeTreeSet (ω₁ ω₂ : List ℕ → ℕ) (t : ℕ) :
    (false, []) ∈ (edgeTreeSet ω₁ ω₂ t : Set (Bool × List ℕ)) := by
  have h := nil_mem_ballTree ω₁ t
  simp only [Finset.mem_coe] at h
  simp only [Finset.mem_coe, edgeTreeSet, Finset.mem_union, Finset.mem_image]
  exact Or.inl ⟨[], h, rfl⟩

theorem true_nil_mem_edgeTreeSet (ω₁ ω₂ : List ℕ → ℕ) (t : ℕ) :
    (true, []) ∈ (edgeTreeSet ω₁ ω₂ t : Set (Bool × List ℕ)) := by
  have h := nil_mem_ballTree ω₂ t
  simp only [Finset.mem_coe] at h
  simp only [Finset.mem_coe, edgeTreeSet, Finset.mem_union, Finset.mem_image]
  exact Or.inr ⟨[], h, rfl⟩

/-- The edge-rooted tree `T̄(t)` built from `(ω₁, ω₂)` (pp. 24–25), as a graph; its root edge has
endpoints `edgeTreeLeft` and `edgeTreeRight`. -/
abbrev edgeTreeBallGraph (ω₁ ω₂ : List ℕ → ℕ) (t : ℕ) :=
  edgeTreeGraph.induce (edgeTreeSet ω₁ ω₂ t : Set (Bool × List ℕ))

/-- The endpoint `(false, [])` of the root edge `e` of `T̄(t)`. -/
def edgeTreeLeft (ω₁ ω₂ : List ℕ → ℕ) (t : ℕ) : (edgeTreeSet ω₁ ω₂ t : Set (Bool × List ℕ)) :=
  ⟨(false, []), false_nil_mem_edgeTreeSet ω₁ ω₂ t⟩

/-- The endpoint `(true, [])` of the root edge `e` of `T̄(t)`. -/
def edgeTreeRight (ω₁ ω₂ : List ℕ → ℕ) (t : ℕ) : (edgeTreeSet ω₁ ω₂ t : Set (Bool × List ℕ)) :=
  ⟨(true, []), true_nil_mem_edgeTreeSet ω₁ ω₂ t⟩

end IsingLTL.FreeEntropy


