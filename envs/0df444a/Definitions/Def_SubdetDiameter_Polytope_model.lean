-- Prove2me | Definitions.Def_SubdetDiameter_Polytope_model
-- name    : SubdetDiameter_Polytope_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:03:38.777991+00:00
-- url     : https://prove2.me/theorems/891aeb54-8639-426e-b04e-7d8062f12c56
-- title:
--   Integer polyhedra, sub-determinant bound, non-degeneracy, vertex volumes and neighbourhoods
-- statement:
--   The model of Bonifas–Di Summa–Eisenbrand–Hähnle–Niemeier for the diameter of an integral polyhedron.
--
--   Let $A \in \mathbb{Z}^{m\times n}$ and $b \in \mathbb{R}^m$, and let $P = \{x \in \mathbb{R}^n : Ax \le b\}$. Write $a_i \in \mathbb{R}^n$ for the $i$-th row of $A$ (`rowVec A i`), so that $P$ is the H-polyhedron $\{x : \langle a_i, x\rangle \le b_i \text{ for all } i\}$. The vertices of $P$ are its extreme points; they form the vertex set $V$ of the polyhedral graph $G_P = (V, E)$, whose edges join the endpoints of the one-dimensional faces of $P$.
--
--   1. **Sub-determinant bound.** $A$ has all sub-determinants bounded by $\Delta \in \mathbb{N}$ in absolute value if
--   $$|\det A_{R,C}| \le \Delta \quad \text{for every } k \ge 1 \text{ and all row indices } R \in [m]^k,\ C \in [n]^k,$$
--   where $A_{R,C}$ is the $k\times k$ submatrix with rows $R$ and columns $C$. This covers the entries ($k=1$) and the minors of every order.
--   2. **Non-degeneracy.** $P$ is non-degenerate if every vertex $v$ of $P$ has exactly $n$ tight inequalities, $|\{i : \langle a_i, v\rangle = b_i\}| = n$.
--   3. **Volume of a set of vertices.** For $U \subseteq V$,
--   $$\mathrm{vol}(U) := \mathrm{vol}\Big(\bigcup_{v\in U} C_v \cap B_n\Big),$$
--   where $C_v = \{c : c^T v \ge c^T x \text{ for all } x \in P\}$ is the normal cone of $P$ at $v$, $B_n$ is the closed Euclidean unit ball, and $\mathrm{vol}$ is Lebesgue measure.
--   4. **Neighbourhood.** For $I \subseteq V$, $\mathcal N(I)$ is the set of vertices not in $I$ that are adjacent in $G_P$ to some vertex of $I$.
--   5. **Breadth-first layers.** For a vertex $v$ and $j \in \mathbb{N}$, $I_j$ is the set of vertices discovered during the first $j$ iterations of breadth-first search from $v$, i.e. the vertices at graph distance at most $j$ from $v$; $I_0 = \{v\}$.
--
--   These objects are the vocabulary of the paper's volume-expansion argument: its main theorem bounds the diameter of $G_P$ in terms of $\Delta$ and $n$ alone.
--
--   **Formalization Note** The polyhedron is `Hirsch.Hpoly (rowVec A) b` and adjacency is `Hirsch.Adj` (the segment $[u,v]$ is an extreme subset, i.e. an edge), both from the published `Hirsch_model`; the normal cone is the published `FirstOrderOpt.ConvexTheory.normalCone`, $\{w : \langle w, y - v\rangle \le 0\ \forall y \in P\}$. Row and column choices in the sub-determinant bound are arbitrary maps $\mathrm{Fin}\,k \to \mathrm{Fin}\,m$, $\mathrm{Fin}\,k\to\mathrm{Fin}\,n$; a repeated index gives determinant $0$. Volumes take values in $[0,\infty]$. `layer P v j` is the set of endpoints of walks of $j$ steps from $v$, each step staying put or crossing an edge.
-- source:
--   Bonifas, Di Summa, Eisenbrand, Hähnle, Niemeier, On Sub-determinants and the Diameter of Polyhedra, Discrete Comput Geom 52 (2014) 102–115, DOI 10.1007/s00454-014-9601-x, p. 103 (polyhedron, vertex, neighbors, diameter), p. 104 (sub-determinant Δ, non-degenerate, normal cone C_v, vol(U), 𝒩(I)), p. 105 (breadth-first layers I_j, proof of Theorem 2)

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

open scoped RealInnerProductSpace

namespace SubdetDiameter.Polytope

/-- Row `i` of an integer matrix `A ∈ ℤ^{m×n}`, as a vector of `ℝ^n`. The polyhedron
`{x : Ax ≤ b}` of the paper is `Hirsch.Hpoly (rowVec A) b`. -/
noncomputable def rowVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (i : Fin m) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => (A i j : ℝ))

/-- `SubdetBound A Δ`: every square submatrix of `A`, of every size `k ≥ 1` (entries,
`2 × 2` minors, …, `n × n` minors), has determinant at most `Δ` in absolute value.
Rows and columns are chosen by arbitrary maps `Fin k → Fin m`, `Fin k → Fin n`; a
non-injective choice repeats a row or column and gives determinant `0`. -/
def SubdetBound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (Δ : ℕ) : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (r : Fin k → Fin m) (c : Fin k → Fin n),
    |(A.submatrix r c).det| ≤ (Δ : ℤ)

/-- The polyhedron `{x : Ax ≤ b}` is **non-degenerate**: each vertex (extreme point) has
exactly `n` tight inequalities. -/
def NonDegenerate {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℝ) : Prop :=
  ∀ v ∈ Set.extremePoints ℝ (Hirsch.Hpoly (rowVec A) b),
    {i : Fin m | ⟪rowVec A i, v⟫ = b i}.ncard = n

/-- The **volume** of a set `U` of vertices of `P`: the Lebesgue measure of the union of
the normal cones `C_v` (`v ∈ U`) intersected with the closed unit ball `B_n`. -/
noncomputable def vertexVol {n : ℕ} (P U : Set (EuclideanSpace ℝ (Fin n))) : ENNReal :=
  MeasureTheory.volume
    (⋃ v ∈ U, FirstOrderOpt.ConvexTheory.normalCone P v ∩ Metric.closedBall 0 1)

/-- The **neighbourhood** `𝒩(I)` of a set `I` of vertices of `P`: the vertices of `P`
that are not in `I` and are adjacent (joined by an edge) to some vertex of `I`. -/
def nbhd {n : ℕ} (P I : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {u | u ∈ Set.extremePoints ℝ P ∧ u ∉ I ∧ ∃ v ∈ I, Hirsch.Adj P u v}

/-- `layer P v j` is the set `I_j` of vertices discovered by the first `j` iterations of
breadth-first search in the vertex-edge graph of `P` started at `v`: the endpoints of the
walks from `v` of `j` steps, each step staying put or crossing an edge. So `layer P v 0 = {v}`
and `layer P v j` is the set of vertices at graph distance at most `j` from `v`. -/
def layer {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (v : EuclideanSpace ℝ (Fin n))
    (j : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {u | ∃ w : ℕ → EuclideanSpace ℝ (Fin n), w 0 = v ∧ w j = u ∧
    ∀ i < j, w i = w (i + 1) ∨ Hirsch.Adj P (w i) (w (i + 1))}

end SubdetDiameter.Polytope


