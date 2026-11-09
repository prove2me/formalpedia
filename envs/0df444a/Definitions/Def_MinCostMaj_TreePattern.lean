-- Prove2me | Definitions.Def_MinCostMaj_TreePattern
-- name    : MinCostMaj_TreePattern
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:13:48.393551+00:00
-- url     : https://prove2.me/theorems/4105b6ad-9b13-4027-a63d-fa3531fe9621
-- title:
--   Tree patterns, realizations and the universal covering pattern
-- statement:
--   A **tree pattern** in an instance $K$ is a finite tree whose vertices are labelled by variables of $K$ and whose edges are labelled by constraints of $K$ consistently with the labels of their endpoints. A **realization** assigns to every vertex a value from the potato of its label so that every edge is satisfied by its constraint. A **universal covering pattern** is an infinite tree pattern covering all finite tree patterns: every copy of a variable $x$ is incident, for every variable $y$ and every $R\in\mathcal R^K_{xy}$, with an edge labelled $R$ to a copy of $y$.
--
--   These objects certify arc-consistent subinstances in the proof that the truncated instance is solvable.
--
--   **Formalization Note** A finite tree pattern is a tree on $\{0,\dots,m-1\}$ with variable labels and a constraint for each oriented edge, the two orientations being opposite readings. The universal covering pattern is the forest of walk trees, one tree per variable: a vertex is a walk in $K$, a copy of its last variable, joined to each one-step extension by an edge labelled with the constraint of that step. A single rooted tree would not cover patterns in other connected components.
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Appendix C.1, p.23 (PDF p.24)

import Mathlib
import Definitions.Def_MinCostMaj_BinInst

namespace MinCostMaj

/-- **Finite tree pattern** in an instance `K` (Appendix C.1, p.23).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, p.23: "A tree pattern in a binary instance K is a finite tree
whose vertices are labeled by variables of K and whose edges are labeled by binary constraints of K
in a way consistent with the endpoint labels."

Vertices `Fin m` with a tree `G`; vertex `i` is labelled by the variable `lab i`; the edge `{i, j}`
read from `i` to `j` is labelled by `R i j ∈ R^K_{lab i, lab j}`, and read from `j` to `i` by the
opposite reading. -/
structure FinTreePattern {V D : Type*} (K : BinInst V D) where
  /-- number of vertices -/
  m : ℕ
  /-- the tree -/
  G : SimpleGraph (Fin m)
  isTree : G.IsTree
  /-- variable labels -/
  lab : Fin m → V
  /-- constraint labels of the oriented edges -/
  R : Fin m → Fin m → Set (D × D)
  mem : ∀ i j, G.Adj i j → R i j ∈ K.rels (lab i) (lab j)
  opp : ∀ i j, G.Adj i j → R j i = Prod.swap ⁻¹' R i j

/-- **Realization of a tree pattern** with values in the potatoes `P` (p.23): "A realization of a
tree pattern assigns to every vertex a value from the potato of its label so that every edge is
satisfied by the corresponding binary constraint." With `P = A^I` for `I ≤ K` this is a realization
in `I` (the constraints of `I` are those of `K` restricted to the potatoes of `I`). -/
def FinTreePattern.IsRealization {V D : Type*} {K : BinInst V D} (t : FinTreePattern K)
    (P : V → Set D) (β : Fin t.m → D) : Prop :=
  (∀ i, β i ∈ P (t.lab i)) ∧ ∀ i j, t.G.Adj i j → (β i, β j) ∈ t.R i j

/-- The last variable of a walk that starts at `x` (steps are stored newest first). -/
def walkEnd {V D : Type*} (x : V) : List (V × Set (D × D)) → V
  | [] => x
  | (y, _) :: _ => y

/-- A walk from `x` in `K`: a list of steps `(y, R)` (newest first), each with
`R ∈ R^K_{z y}` where `z` is the end of the walk so far. -/
def IsWalk {V D : Type*} (K : BinInst V D) (x : V) : List (V × Set (D × D)) → Prop
  | [] => True
  | (y, R) :: w => IsWalk K x w ∧ R ∈ K.rels (walkEnd x w) y

/-- The vertices of the **universal covering pattern** of `K`: walks `(x, w)` of `K`. The vertex
`(x, w)` is a copy of the variable `walkEnd x w`; it is joined to each one-step extension
`(x, (y, R) :: w)` by an edge labelled `R`. -/
def CoverVert {V D : Type*} (K : BinInst V D) : Type _ :=
  {p : V × List (V × Set (D × D)) // IsWalk K p.1 p.2}

/-- **Realization of the universal covering pattern** of `K` with values in the potatoes `P`
(p.23): "A universal covering pattern for K is an infinite tree pattern that covers all finite tree
patterns in K. Every copy of a variable x is incident, for every variable y and every R ∈ R^K_xy,
with an edge labelled by R leading to a copy of y."

**Formalization Note.** The covering pattern is the forest of walk trees, one tree per variable
(its root is the empty walk from `x`): each vertex, a copy of `z`, has for every `y` and every
`R ∈ R^K_{zy}` a child edge labelled `R` to a copy of `y`. A single rooted tree would not cover
tree patterns in other connected components of `K`. -/
def IsCoverRealization {V D : Type*} (K : BinInst V D) (P : V → Set D) (β : CoverVert K → D) :
    Prop :=
  (∀ v : CoverVert K, β v ∈ P (walkEnd v.1.1 v.1.2)) ∧
    ∀ (v : CoverVert K) (y : V) (R : Set (D × D)) (h : IsWalk K v.1.1 ((y, R) :: v.1.2)),
      (β v, β ⟨(v.1.1, (y, R) :: v.1.2), h⟩) ∈ R

end MinCostMaj


