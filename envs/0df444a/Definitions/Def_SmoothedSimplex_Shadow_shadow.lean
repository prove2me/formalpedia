-- Prove2me | Definitions.Def_SmoothedSimplex_Shadow_shadow
-- name    : SmoothedSimplex_Shadow_shadow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:04:50.241445+00:00
-- url     : https://prove2.me/theorems/3d13384c-4028-4164-9755-1b5e413e29d4
-- title:
--   Definition 3.2.4 — the shadow $\mathrm{Shadow}_{t,z}(a_1,\dots,a_n)$
-- statement:
--   For linearly independent $t,z\in\mathbb R^d$ and $a_1,\dots,a_n\in\mathbb R^d$,
--
--   $$
--   \mathrm{Shadow}_{t,z}(a_1,\dots,a_n)=\bigcup_{q\in\mathrm{Span}(t,z)}\{\mathrm{optSimp}_q(a_1,\dots,a_n)\},
--   $$
--
--   the set of index sets $I$ that are optimal for some objective direction $q$ in the plane spanned by $t$ and $z$. Its size $|\mathrm{Shadow}_{t,z}|$ is the number of vertices of the projection ("shadow") of the polyhedron $\{x:\langle a_i|x\rangle\le 1\}$ onto $\mathrm{Span}(t,z)$, which bounds the number of pivots of the shadow-vertex simplex method.
--
--   **Formalization Note** The elements of the shadow are index sets: $I\in\mathrm{Shadow}_{t,z}$ iff $I\in\mathrm{optSimp}_q$ for some nonzero $q\in\mathrm{Span}(t,z)$; the size is the cardinality of this finite set (the paper counts it this way, p. 59). The direction $q=0$ is excluded: $0$ lies in every cone, so $\mathrm{optSimp}_0$ contains every facet of $\mathrm{ConvHull}(0,a_1,\dots,a_n)$ avoiding the origin, which is not part of the shadow; the paper only uses the nonzero directions $q_\theta=z\sin\theta+t\cos\theta$. The definition is stated for all $t,z$; theorems assume independence.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Definition 3.2.4, printed p. 32 (PDF p. 32)

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_optSimp

namespace SmoothedSimplex.Shadow

open Classical in
/-- `Shadow_{t,z}(a₁, …, aₙ)` with `y = 1` (Spielman & Teng, arXiv:cs/0111050v7,
Definition 3.2.4, printed p. 32, PDF p. 32):
`Shadow_{t,z}(a₁, …, aₙ) = ⋃_{q ∈ Span(t,z)} {optSimp_q(a₁, …, aₙ)}`.
Its size `|Shadow_{t,z}(a)|` is `(shadow t z a).card`.

**Formalization Note.**
* The elements of the shadow are index sets `I`: `I ∈ shadow t z a` iff `I ∈ optSimp_q(a)` for
  some `q ∈ Span(t, z)`. This is how the paper counts it (proof of Proposition 5.0.2, p. 59:
  the shadow is bounded by the `C(n,d)` `d`-subsets of `[n]`); read literally, the braces would
  make it a set of values of `optSimp`, including `∅`.
* `q = 0` is excluded. Since `0 ∈ Cone(A_I)` for every `I`, `optSimp_0(a)` contains every facet
  of `ConvHull(0, a)` not through the origin, so including `q = 0` would make the shadow the
  set of all such facets (all vertices of the polytope), not the shadow polygon's vertices.
  The paper's proof only ever uses the directions `q_θ = z sin θ + t cos θ ≠ 0` (eq. (11), p. 39),
  and `optSimp_q = optSimp_{λq}` for `λ > 0`.
* The paper defines the shadow for independent `t, z`; the definition itself makes sense for
  all `t, z`, and every statement using it assumes the paper's hypothesis. -/
noncomputable def shadow {d n : ℕ} (t z : EuclideanSpace ℝ (Fin d))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) : Finset (Finset (Fin n)) :=
  Finset.univ.filter
    (fun I => ∃ q ∈ Submodule.span ℝ {t, z}, q ≠ 0 ∧ I ∈ optSimp q a)

end SmoothedSimplex.Shadow


