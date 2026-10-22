-- Prove2me | Definitions.Def_LeeSviridenkoVondrak_LocalSearch_Exchange
-- name    : LeeSviridenkoVondrak_LocalSearch_Exchange
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:49:33.91233+00:00
-- url     : https://prove2.me/theorems/4ade4c53-108b-4719-bea8-b261f132635b
-- title:
--   Exchange digraphs, irreducible cycles, and feasible paths
-- statement:
--   For an independent set $I$, the first exchange digraph has arcs $x\to y$ with $x\in I$, $y\notin I$ and $I-x+y$ independent in $M_1$; the second reverses these arcs for $M_2$. Their union is the two-matroid exchange digraph. A matching is an unoriented edge set in one constituent, with exactly one mate for each vertex on each side. A directed path or cycle has distinct vertices; paths may have one vertex, cycles have at least two. An irreducible cycle has a unique perfect matching in each constituent on its vertices. A feasible path or cycle allows the swap of its full vertex set and the swap of every subpath whose endpoints are endpoints of the whole path or belong to $I$:
--   $$I\mathbin{\triangle}V(A')\in\mathcal F_1\cap\mathcal F_2.$$
--   These are Definitions 2.1–2.2. They retain the subpath condition needed by the exchange analysis.
--
--   **Formalization Note** Vertex lists are ordered and without repetitions, while indexed collections of paths or cycles may repeat. A cycle has no endpoints. Subpaths include wraparound segments of cycles, and symmetric difference counts vertices only. The predicates are total on arbitrary $I$ and Mathlib matroids; all source theorems impose the whole-ground and independent-$I$ standing assumptions explicitly.
-- source:
--   Lee, Sviridenko and Vondrák (2010), Submodular Maximization over Multiple Matroids via Generalized Exchange Properties, Mathematics of Operations Research 35(4), 795–806, https://doi.org/10.1287/moor.1100.0463; §2.1, Definitions 2.1–2.2, pp. 798–799 / PDF 4–5

import Definitions.Def_LeeSviridenkoVondrak_LocalSearch_Model

open scoped symmDiff

namespace LeeSviridenkoVondrak.LocalSearch

/-- Constituent-one orientation: inside to outside; constituent two reverses it. -/
def ExchangeArc {n : ℕ} (M : Matroid (Fin n)) (I : Finset (Fin n))
    (x y : Fin n) : Prop :=
  x ∈ I ∧ y ∉ I ∧ M.Indep (↑(insert y (I.erase x)) : Set (Fin n))

def TwoArc {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (I : Finset (Fin n))
    (x y : Fin n) : Prop := ExchangeArc M₁ I x y ∨ ExchangeArc M₂ I y x

/-- An unoriented matching in one constituent digraph, encoded without choice of
an ordering of its edges. Each endpoint has exactly one mate. -/
def PerfectMatching {n : ℕ} (M : Matroid (Fin n)) (I L R : Finset (Fin n))
    (E : Finset (Fin n × Fin n)) : Prop :=
  (∀ e ∈ E, e.1 ∈ L ∧ e.2 ∈ R ∧ ExchangeArc M I e.1 e.2) ∧
  (∀ x ∈ L, ∃! y, (x, y) ∈ E) ∧ (∀ y ∈ R, ∃! x, (x, y) ∈ E)

/-- A simple directed path or cycle is encoded by a nonempty list of distinct
vertices; cycles close the last-to-first edge and have at least two vertices. -/
structure WalkData (n : ℕ) where
  vertices : List (Fin n)
  closed : Bool

def WalkData.support {n : ℕ} (A : WalkData n) : Finset (Fin n) := A.vertices.toFinset

def WalkData.edge {n : ℕ} (A : WalkData n) (x y : Fin n) : Prop :=
  (x, y) ∈ A.vertices.zip A.vertices.tail ∨
    (A.closed = true ∧ A.vertices.getLast? = some x ∧ A.vertices.head? = some y)

def WalkData.endpoint {n : ℕ} (A : WalkData n) (x : Fin n) : Prop :=
  A.closed = false ∧ (A.vertices.head? = some x ∨ A.vertices.getLast? = some x)

def IsDirected {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (I : Finset (Fin n))
    (A : WalkData n) : Prop :=
  A.vertices ≠ [] ∧ A.vertices.Nodup ∧ (A.closed = true → 2 ≤ A.vertices.length) ∧
    ∀ x y, A.edge x y → TwoArc M₁ M₂ I x y

/-- Every simple directed subpath, including singleton paths and cyclic wraparound.
Edge inclusion in a simple whole path/cycle is precisely contiguous subpath inclusion. -/
def IsSubpath {n : ℕ} (A B : WalkData n) : Prop :=
  B.closed = false ∧ B.vertices ≠ [] ∧ B.vertices.Nodup ∧
    B.support ⊆ A.support ∧ ∀ x y, B.edge x y → A.edge x y

/-- Definition 2.1: uniqueness is in each constituent, never in the union. -/
def Irreducible {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (I : Finset (Fin n))
    (A : WalkData n) : Prop :=
  IsDirected M₁ M₂ I A ∧ A.closed = true ∧
    (∃! E, PerfectMatching M₁ I (I ∩ A.support) (A.support \ I) E) ∧
    (∃! E, PerfectMatching M₂ I (I ∩ A.support) (A.support \ I) E)

/-- Definition 2.2 includes the full swap and every endpoint-admissible subpath swap.
A closed cycle has no endpoints. Symmetric difference uses vertices, not traversals. -/
def FeasibleWalk {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (I : Finset (Fin n))
    (A : WalkData n) : Prop :=
  IsDirected M₁ M₂ I A ∧
  (M₁.Indep (↑(I ∆ A.support) : Set (Fin n)) ∧
   M₂.Indep (↑(I ∆ A.support) : Set (Fin n))) ∧
  ∀ B, IsSubpath A B → (∀ x, B.endpoint x → A.endpoint x ∨ x ∈ I) →
    M₁.Indep (↑(I ∆ B.support) : Set (Fin n)) ∧
    M₂.Indep (↑(I ∆ B.support) : Set (Fin n))

end LeeSviridenkoVondrak.LocalSearch


