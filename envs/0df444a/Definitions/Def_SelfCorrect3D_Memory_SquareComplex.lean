-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_SquareComplex
-- name    : SelfCorrect3D_Memory_SquareComplex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:48.672351+00:00
-- url     : https://prove2.me/theorems/eecdd581-c7ef-4706-ad51-8b346a1ebc8b
-- title:
--   Finite square complex, degrees, square images, $(t,\ell)$-embeddings
-- statement:
--   A **finite square complex** on a finite vertex set $V$ consists of a set of edges (unordered pairs of distinct vertices) and a set of squares, each given by four distinct vertices $(v_0,v_1,v_2,v_3)$ whose cyclically consecutive pairs are edges. The **vertex degree** of $v$ is the number of edges at $v$; the **edge degree** of $e$ is the number of squares having $e$ as a side.
--
--   For a vertex map $I:V\to\mathbb R^3$, the **image of a square** is obtained by linear interpolation as the union of the two triangles $\mathrm{conv}\{Iv_0,Iv_1,Iv_2\}\cup\mathrm{conv}\{Iv_0,Iv_2,Iv_3\}$. The map $I$ is a **$(t,\ell)$-embedding** (Definition 3.1) if
--
--   1. (Bounded density) every closed unit ball in $\mathbb R^3$ meets the images of at most $t$ squares, and
--   2. (Geometric locality) the endpoints of every edge are mapped to points at distance at most $\ell$.
--
--   **Formalization Note** Squares are ordered 4-tuples; the triangulation along the diagonal $v_0v_2$ follows step 1 of the perturbation procedure (p. 23: "We formally add diagonal lines to the square 2-cells").
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, §2.2, p. 11; §3, pp. 21–22; Definition 3.1, pp. 22–23

import Mathlib

namespace SelfCorrect3D.Memory

/-- **Finite square complex.** Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943, §2.2, p. 11 (Tanner square
complexes) and §3, p. 22 (`z_v`: "edges incident to a vertex", `z_e`: "faces incident to an
edge"). Vertices `V`, a finite set of edges (no loops), and a finite set of squares, each given by
four distinct vertices `(v₀, v₁, v₂, v₃)` whose cyclically consecutive pairs are edges.

**Formalization Note.** A square is an ordered 4-tuple; listing the same boundary cycle twice
(e.g. rotated) gives two squares. -/
structure SquareComplex (V : Type) : Type where
  /-- The edges (1-cells). -/
  edges : Finset (Sym2 V)
  /-- No loops. -/
  edges_not_diag : ∀ e ∈ edges, ¬ e.IsDiag
  /-- The squares (2-cells), each as its cyclically ordered vertices. -/
  squares : Finset (Fin 4 → V)
  /-- The four vertices of a square are distinct. -/
  squares_inj : ∀ s ∈ squares, Function.Injective s
  /-- Consecutive vertices of a square span an edge. -/
  squares_edges : ∀ s ∈ squares, ∀ i : Fin 4, s(s i, s (i + 1)) ∈ edges

namespace SquareComplex

variable {V : Type}

/-- Vertex degree: the number of edges incident to `v`. -/
def vertexDegree [DecidableEq V] (X : SquareComplex V) (v : V) : ℕ :=
  (X.edges.filter fun e => v ∈ e).card

/-- Edge degree: the number of squares having `e` as a side. -/
def edgeDegree [DecidableEq V] (X : SquareComplex V) (e : Sym2 V) : ℕ :=
  (X.squares.filter fun s => ∃ i : Fin 4, s(s i, s (i + 1)) = e).card

/-- Image of a square under a vertex map `I : V → ℝ³`, extended by linear interpolation:
the two triangles `conv{I v₀, I v₁, I v₂} ∪ conv{I v₀, I v₂, I v₃}` along the diagonal `v₀v₂`
(§3, p. 21: "The image of edges and higher-dimensional cells are then obtained via linear
interpolation"; p. 23, step 1: "We formally add diagonal lines to the square 2-cells"). -/
def squareImage (I : V → EuclideanSpace ℝ (Fin 3)) (s : Fin 4 → V) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  convexHull ℝ {I (s 0), I (s 1), I (s 2)} ∪ convexHull ℝ {I (s 0), I (s 2), I (s 3)}

open Classical in
/-- **`(t, ℓ)`-embedding in ℝ³**, Definition 3.1, pp. 22–23: (1) (Bounded density) every closed
unit ball of ℝ³ meets the images of at most `t` squares; (2) (Geometric locality) the endpoints of
every edge map to points at distance at most `ℓ`. -/
noncomputable def IsEmbedding (X : SquareComplex V) (I : V → EuclideanSpace ℝ (Fin 3)) (t : ℕ)
    (ℓ : ℝ) : Prop :=
  (∀ x : EuclideanSpace ℝ (Fin 3),
      (X.squares.filter fun s => (squareImage I s ∩ Metric.closedBall x 1).Nonempty).card ≤ t) ∧
    ∀ u v : V, s(u, v) ∈ X.edges → dist (I u) (I v) ≤ ℓ

end SquareComplex

end SelfCorrect3D.Memory


