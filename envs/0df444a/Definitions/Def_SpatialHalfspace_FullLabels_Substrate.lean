-- Prove2me | Definitions.Def_SpatialHalfspace_FullLabels_Substrate
-- name    : SpatialHalfspace_FullLabels_Substrate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:14:21.451755+00:00
-- url     : https://prove2.me/theorems/ae72738a-cf4f-4c47-89ac-1675c11b9f84
-- title:
--   Definition 2.1 — $p$-dimensional communication substrate
-- statement:
--   Let $U$ be a set of terminals and $p\ge 1$ a physical dimension. A **$p$-dimensional substrate** consists of
--
--   1. a finite connected undirected graph $G=(V,E_G)$;
--   2. an injection $\iota:U\hookrightarrow V$ placing the terminals at vertices;
--   3. an output vertex $r_\star\in V$, the **root** (not necessarily a terminal);
--   4. a placement $\varphi:V\to\mathbb R^p$;
--   5. positive link lengths $\ell_{xy}>0$ for the edges $xy\in E_G$,
--
--   such that
--
--   $$\ell_{xy}\ \ge\ \|\varphi(x)-\varphi(y)\|_2\quad(xy\in E_G),\qquad \|\varphi(\iota(u))-\varphi(\iota(v))\|_2\ \ge\ 1\quad(u\ne v).$$
--
--   Only terminals must be unit-separated: auxiliary vertices may be placed anywhere (even on top of each other) and wires may cross. No bandwidth or wire-area constraint is imposed.
--
--   Derived notions: the edge boundary $\partial_G W$ of $W\subseteq V$ (edges with exactly one endpoint in $W$), the distance to the root $d(v)=\|\varphi(v)-\varphi(r_\star)\|_2$, and the balls $W_t=\{v\in V: d(v)\le t\}$ (§4).
--
--   **Formalization Note** The vertex set is $\{0,\dots,N-1\}$ (`Fin N`), which loses no generality for a finite graph; the graph is a Mathlib `SimpleGraph`. Each edge is listed once as an ordered pair $(x,y)$ with $x<y$. Link lengths are a symmetric function whose values off the edges are irrelevant.
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 5, PDF p. 6, Definition 2.1, eq. (6), PDF p. 6; d(v) and W_t from §4, PDF p. 11

import Mathlib

/-!
# Communication substrates (Yang, STOC 2027 submission #119, Definition 2.1, printed p. 5)

A `p`-dimensional substrate for a terminal set `U` is a finite connected undirected graph
`G = (V, E_G)` (here `V = Fin N`), an injection `ι : U ↪ V`, a root `r⋆ ∈ V`, a placement
`φ : V → ℝ^p` and positive link lengths `ℓ_{xy} ≥ ‖φ(x) − φ(y)‖₂`, with the terminals
unit-separated: `‖φ(ι u) − φ(ι v)‖₂ ≥ 1` for `u ≠ v`. Auxiliary vertices are unconstrained
(they may coincide), the root need not be a terminal and wires may cross.
-/

namespace SpatialHalfspace.FullLabels

/-- Physical space `ℝ^p` with the Euclidean norm. -/
abbrev Phys (p : ℕ) := EuclideanSpace ℝ (Fin p)

/-- Definition 2.1: a `p`-dimensional communication substrate for the terminal set `U`. -/
structure Substrate (p : ℕ) (U : Type) where
  /-- number of vertices; the vertex set is `Fin N` -/
  N : ℕ
  /-- the finite undirected graph `G` -/
  graph : SimpleGraph (Fin N)
  connected : graph.Connected
  /-- the injection of terminals into vertices -/
  ι : U → Fin N
  ι_injective : Function.Injective ι
  /-- the output vertex `r⋆` -/
  root : Fin N
  /-- the placement `φ : V → ℝ^p` -/
  φ : Fin N → Phys p
  /-- link lengths `ℓ_{xy}` (only their values on edges matter) -/
  ℓ : Fin N → Fin N → ℝ
  ℓ_symm : ∀ x y, ℓ x y = ℓ y x
  ℓ_pos : ∀ x y, graph.Adj x y → 0 < ℓ x y
  dist_le_ℓ : ∀ x y, graph.Adj x y → dist (φ x) (φ y) ≤ ℓ x y
  /-- terminals are unit-separated -/
  unit_sep : ∀ u v, u ≠ v → 1 ≤ dist (φ (ι u)) (φ (ι v))

namespace Substrate

variable {p : ℕ} {U : Type} (S : Substrate p U)

/-- The edges of `G`, each listed once as an ordered pair `(x, y)` with `x < y`. -/
def Edge : Type := {e : Fin S.N × Fin S.N // e.1 < e.2 ∧ S.graph.Adj e.1 e.2}

noncomputable instance : Fintype S.Edge := by
  classical
  exact (Subtype.fintype _ : Fintype {e : Fin S.N × Fin S.N // e.1 < e.2 ∧ S.graph.Adj e.1 e.2})

noncomputable instance : DecidableEq S.Edge := Classical.decEq _

/-- The edge boundary `∂_G W`: edges with exactly one endpoint in `W`. -/
def boundary (W : Set (Fin S.N)) : Set S.Edge := {e | (e.1.1 ∈ W ∧ e.1.2 ∉ W) ∨ (e.1.1 ∉ W ∧ e.1.2 ∈ W)}

/-- The length `ℓ_f` of an edge. -/
def edgeLength (e : S.Edge) : ℝ := S.ℓ e.1.1 e.1.2

/-- `d(v) = ‖φ(v) − φ(r⋆)‖₂`, the distance from `v` to the root. -/
noncomputable def rootDist (v : Fin S.N) : ℝ := dist (S.φ v) (S.φ S.root)

/-- `W_t = {v ∈ V : d(v) ≤ t}`. -/
def ball (t : ℝ) : Set (Fin S.N) := {v | S.rootDist v ≤ t}

end Substrate

end SpatialHalfspace.FullLabels


