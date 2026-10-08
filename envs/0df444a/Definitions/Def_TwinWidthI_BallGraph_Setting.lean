-- Prove2me | Definitions.Def_TwinWidthI_BallGraph_Setting
-- name    : TwinWidthI_BallGraph_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:10.095347+00:00
-- url     : https://prove2.me/theorems/a6183bd4-d5b8-42b9-860a-d87db1c964f9
-- title:
--   pp. 3:11–3:16 — twin-width (partition form), red twin-width, d-dimensional grids, grids with diagonals, unit ball graphs, grid cells
-- statement:
--   Let $V$ be a finite vertex set and $G$, $H$ simple graphs on $V$.
--
--   **Twin-width.** Two vertex sets $X, Y\subseteq V$ are *homogeneous* in $G$ if either every pair $(x,y)\in X\times Y$ is an edge of $G$ or no pair is. For a partition $\mathcal P$ of $V$, a part $X$ has *red degree* equal to the number of other parts $Y\neq X$ of $\mathcal P$ that are not homogeneous to $X$; $\mathcal P$ is a *$d$-partition* if every part has red degree at most $d$. A *merge step* replaces two distinct parts $X,Y$ of a partition by $X\cup Y$. The graph $G$ has *twin-width at most $d$*, written $\operatorname{tww}(G)\le d$, if there is a sequence of partitions
--   $$\mathcal P_0,\ \mathcal P_1,\ \dots,\ \mathcal P_N$$
--   of $V$ in which $\mathcal P_0$ is the partition into singletons, $\mathcal P_N$ has at most one part, each $\mathcal P_{i+1}$ arises from $\mathcal P_i$ by one merge step, and every $\mathcal P_i$ is a $d$-partition.
--
--   **Red twin-width.** Let $H^r=(V,\emptyset,E(H))$ be the trigraph whose edges are all red. Two vertex sets $X,Y$ are *joined* in $H$ if some edge of $H$ has one end in $X$ and the other in $Y$. A partition is a *red $d$-partition* of $H$ if every part is joined to at most $d$ other parts, and $\operatorname{tww}(H^r)\le d$ is defined as above with red $d$-partitions in place of $d$-partitions.
--
--   **Grids.** For $d,n\ge 0$ let $[n]^d$ be the set of $d$-tuples with entries in $\{0,\dots,n-1\}$. The *$d$-dimensional $n$-grid* $P^d_n$ has vertex set $[n]^d$, with $x$ and $y$ adjacent if and only if
--   $$\sum_{i=1}^d |x_i-y_i| = 1.$$
--   The *$d$-dimensional $n$-grid with diagonals* $K_{n,d}$ has vertex set $[n]^d$, with distinct $x,y$ adjacent if and only if $\max_i |x_i-y_i|\le 1$; $K^r_{n,d}$ is the trigraph $([n]^d,\emptyset,E(K_{n,d}))$.
--
--   **Unit ball graphs.** Given points $c(v)\in\mathbb R^d$ ($v\in V$), the *unit $d$-dimensional ball graph* with these centres joins distinct $u,v$ if and only if the closed unit balls around $c(u)$ and $c(v)$ meet, that is,
--   $$\|c(u)-c(v)\|_2\le 2 .$$
--
--   **Cells.** For $z\in\mathbb Z^d$, the cell $Q_z$ of the regular grid of spacing $2/\sqrt d$ is the half-open cube
--   $$Q_z=\prod_{i=1}^d \Bigl[\,z_i\tfrac{2}{\sqrt d},\ (z_i+1)\tfrac{2}{\sqrt d}\Bigr).$$
--   Its largest diagonal has length exactly $2$.
--
--   These are the objects of Theorems 4.3 and 4.5 and Lemma 4.4.
--
--   **Formalization Note.** Twin-width is stated in the paper's equivalent partition form (p. 3:12: in a contraction sequence there is a red edge between two contracted vertices exactly when their vertex sets are not homogeneous; p. 3:32: sequences of $d$-partitions); trigraphs are not formalized. For the all-red trigraph $(V,\emptyset,E(H))$, the contraction rule of p. 3:11 (a new edge $wx$ is black iff both $ux$ and $vx$ are black, absent iff neither $ux$ nor $vx$ is an edge of any colour, red otherwise) never creates a black edge, so by induction two contracted vertices are red-adjacent exactly when some edge of $H$ joins their vertex sets: this is `RedTwinWidthLE`. Twin-width is never a number here: $\operatorname{tww}(G)\le d$ is the predicate `TwinWidthLE G d`, so no infimum over an empty set occurs; the final partition has *at most* one part, which covers the empty vertex set. $[n]^d$ is `Fin d → Fin n` (coordinates $0,\dots,n-1$ instead of $1,\dots,n$). Balls are closed of radius $1$ (adjacency at distance exactly $2$ included), as fixed by the proof of Theorem 4.5 (p. 3:16). In `cell`, Lean's convention $2/0=0$ makes the cell for $d=0$ the whole (one-point) space.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), pp. 3:11–3:12 §3 (trigraphs, contractions, twin-width), p. 3:32 §7.1 (d-partitions), pp. 3:14–3:15 §4.2 (d-dimensional n-grid, grid with diagonals K_{n,d}, K^r_{n,d}), p. 3:16 proof of Theorem 4.5 (unit balls, grid of spacing 2/√d)

import Mathlib
import Definitions.Def_TwinWidthI_BoolWidth_Setting

namespace TwinWidthI.BallGraph

open Finset

/-! ### Graph twin-width in partition form (pp. 3:11–3:12, p. 3:32) -/

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in

/-! ### Twin-width of the all-red trigraph `(V, ∅, E(H))` (§3, p. 3:11; §4.2, pp. 3:15–3:16) -/

/-- Some edge of `H` joins the vertex sets `X` and `Y`. In the trigraph `(V, ∅, E(H))` with no
black edge, the contraction rule of p. 3:11 makes two contracted vertices red-adjacent exactly
when some edge of `H` joins the vertex sets they stand for. -/
def SomeEdge (H : SimpleGraph V) (X Y : Finset V) : Prop := ∃ x ∈ X, ∃ y ∈ Y, H.Adj x y

open Classical in
/-- `P` is a d-partition of the all-red trigraph `(V, ∅, E(H))`: every part is joined by some
edge of `H` to at most `d` other parts. -/
def IsRedDPartition (H : SimpleGraph V) (P : Finpartition (univ : Finset V)) (d : ℕ) : Prop :=
  ∀ X ∈ P.parts, #{Y ∈ P.parts | Y ≠ X ∧ SomeEdge H X Y} ≤ d

/-- The trigraph `(V, ∅, E(H))`, in which every edge of `H` is red, has twin-width at most `d`:
a sequence of red d-partitions from the singletons to at most one part, each obtained from the
previous by merging two parts. -/
def RedTwinWidthLE (H : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ (N : ℕ) (P : Fin (N + 1) → Finpartition (univ : Finset V)),
    P 0 = ⊥ ∧ #(P (Fin.last N)).parts ≤ 1 ∧
    (∀ i : Fin N, TwinWidthI.BoolWidth.IsMergeStep (P i.castSucc) (P i.succ)) ∧
    ∀ i, IsRedDPartition H (P i) d

end TwinWidthI.BallGraph

namespace TwinWidthI.BallGraph

/-! ### Grids, grids with diagonals, unit ball graphs (§4.2, pp. 3:14–3:16) -/

/-- pp. 3:14–3:15: the d-dimensional n-grid `P^d_n` on `[n]^d` (here `Fin d → Fin n`), with an
edge between `x` and `y` iff `∑ᵢ |xᵢ − yᵢ| = 1`. -/
def grid (d n : ℕ) : SimpleGraph (Fin d → Fin n) where
  Adj x y := ∑ i, |((x i : ℕ) : ℤ) - ((y i : ℕ) : ℤ)| = 1
  symm := ⟨fun x y h => by simpa only [abs_sub_comm] using h⟩
  loopless := ⟨fun x h => by simp at h⟩

/-- p. 3:15: the d-dimensional n-grid with diagonals `K_{n,d}` on `[n]^d`, with an edge between
two distinct `x`, `y` iff `maxᵢ |xᵢ − yᵢ| ≤ 1`. -/
def kingGraph (d n : ℕ) : SimpleGraph (Fin d → Fin n) where
  Adj x y := x ≠ y ∧ ∀ i, |((x i : ℕ) : ℤ) - ((y i : ℕ) : ℤ)| ≤ 1
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun i => by rw [abs_sub_comm]; exact h.2 i⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The unit d-dimensional ball graph with centres `c v ∈ ℝ^d`: the intersection graph of the
closed balls of radius 1 centred at the `c v`, i.e. distinct `u`, `v` are adjacent iff
`‖c u − c v‖ ≤ 2` (p. 3:16: "a largest diagonal of each hypercubic cell has length exactly 2.
Hence the unit balls centered within a given cell form a clique"). -/
def ballGraph {V : Type*} {d : ℕ} (c : V → EuclideanSpace ℝ (Fin d)) : SimpleGraph V where
  Adj u v := u ≠ v ∧ dist (c u) (c v) ≤ 2
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [dist_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Proof of Theorem 4.5, p. 3:16: the cell of the regular grid of spacing `2/√d` indexed by
`z ∈ ℤ^d`, the half-open cube `∏ᵢ [zᵢ·2/√d, (zᵢ+1)·2/√d)`. -/
def cell {d : ℕ} (z : Fin d → ℤ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {p | ∀ i, (z i : ℝ) * (2 / Real.sqrt d) ≤ p i ∧ p i < ((z i : ℝ) + 1) * (2 / Real.sqrt d)}

end TwinWidthI.BallGraph


