-- Prove2me | Definitions.Def_StochMatchPoly_load
-- name    : StochMatchPoly_load
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:14:05.853955+00:00
-- url     : https://prove2.me/theorems/c6f8c603-fb86-42c7-841a-56ef3d33604a
-- title:
--   Edge vectors: total weight $|z|$, vertex loads $z_v$, fractional matchings, and the load repair of Lemma 4.4
-- statement:
--   Let $K$ be a finite simple graph and $z$ a nonnegative edge vector. Write
--
--   $$|z|=\sum_e z_e,\qquad z_v=\sum_{e\ni v}z_e ,$$
--
--   the sums over the edges of $K$. The vector $z$ is a **fractional matching** if $z_v\le 1$ for every vertex $v$. For a nonnegative edge vector $x$, the **repaired vector** is
--
--   $$y_{uv}=\frac{x_{uv}}{\max\{1,x_u,x_v\}} .$$
--
--   These are the objects of Lemmas 4.3 and 4.4, which turn the fractional assignment of the main proof into an integral matching.
--
--   **Formalization Note** Edge vectors are functions `Sym2 V → ℝ`, of which only the values on the edges of $K$ are used. The denominator of the repair is at least $1$.
-- source:
--   S. Behnezhad, Stochastic Matching with Polynomial Degree, arXiv:2611.03367 (preprint, held version, sha256 409beb43bd8ab862a4a4a595be9c08afd92590790382102cb640d81d9b564017), §4.1 p.9 (PDF p.10); Lemma 4.4, p.10 (PDF p.11)

import Mathlib

open Classical

namespace StochMatchPoly

/-! # Edge vectors: total weight, vertex loads, fractional matchings, the load repair

S. Behnezhad, *Stochastic Matching with Polynomial Degree*, arXiv:2611.03367 (held version,
sha256 409beb43…), §4.1, p.9 (PDF p.10), and Lemma 4.4, p.10 (PDF p.11).

"For a nonnegative edge vector z, use |z| := Σ_e z_e, z_v := Σ_{e∋v} z_e, z(F) := Σ_{e∈F} z_e.
The vector is a fractional matching if z_v ≤ 1 for every vertex."
"For any nonnegative edge vector x, put y_uv = x_uv / max{1, x_u, x_v}."

**Formalization Note.** The graph `K` is a `SimpleGraph` on a finite vertex type, and an edge
vector is a function `z : Sym2 V → ℝ` of which only the values on the edges `K.edgeFinset` are
used. `load K z v` is `z_v`, the sum over the edges of `K` containing `v`; `total K z` is `|z|`.
A fractional matching is nonnegative on the edges with every load at most `1`. `repair K x` is the
rescaled vector of Lemma 4.4; on the edge `s(u, v)` it is `x_uv / max{1, x_u, x_v}` (the
denominator is at least `1`, so no division by zero occurs). -/

variable {V : Type*} [Fintype V]

/-- `|z| = Σ_e z_e`, the total weight of `z` on the edges of `K`. -/
noncomputable def total (K : SimpleGraph V) (z : Sym2 V → ℝ) : ℝ :=
  ∑ e ∈ K.edgeFinset, z e

/-- The load `z_v = Σ_{e∋v} z_e` of the vertex `v`, over the edges of `K` containing `v`. -/
noncomputable def load (K : SimpleGraph V) (z : Sym2 V → ℝ) (v : V) : ℝ :=
  ∑ e ∈ K.edgeFinset.filter (fun e => v ∈ e), z e

/-- `z` is a fractional matching of `K`: nonnegative on the edges and `z_v ≤ 1` at every vertex. -/
def IsFracMatching (K : SimpleGraph V) (z : Sym2 V → ℝ) : Prop :=
  (∀ e ∈ K.edgeFinset, 0 ≤ z e) ∧ ∀ v, load K z v ≤ 1

/-- The repaired vector of Lemma 4.4: `y_uv = x_uv / max{1, x_u, x_v}`. -/
noncomputable def repair (K : SimpleGraph V) (x : Sym2 V → ℝ) (e : Sym2 V) : ℝ :=
  x e / Sym2.lift ⟨fun u v => max 1 (max (load K x u) (load K x v)),
    fun u v => by simp only [max_comm (load K x u)]⟩ e

end StochMatchPoly


