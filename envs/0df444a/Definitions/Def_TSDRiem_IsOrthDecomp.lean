-- Prove2me | Definitions.Def_TSDRiem_IsOrthDecomp
-- name    : TSDRiem_IsOrthDecomp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:25:30.86361+00:00
-- url     : https://prove2.me/theorems/dd9c6a9f-ad5d-4c97-81b0-352bf7248eca
-- title:
--   Orthogonal decomposition of a Hilbert space (§4.1)
-- statement:
--   Let $V$ be a real inner product space. A family of orthogonal projections $\{P'_k\}_{k\in[m]}$ is an **orthogonal decomposition** of $V$ if
--
--   $$
--   \operatorname{Im}(P'_i)\perp\operatorname{Im}(P'_j)\ \ (i\ne j)
--   \qquad\text{and}\qquad
--   \operatorname{Span}\Big(\bigcup_{k\in[m]}\operatorname{Im}(P'_k)\Big)=V .
--   $$
--
--   In block coordinate descent on $\mathbb R^n$ the coordinate blocks give such a decomposition. On a manifold, Assumption 4.2 asks that the transported projections $P_{t,k}$ be close to one.
--
--   **Formalization Note** The projections are recorded by their images $K_k$, and $P'_k$ is the orthogonal projection onto $K_k$. The printed "$\operatorname{Im}(P_j)$" is read as $\operatorname{Im}(P'_j)$.
-- source:
--   Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, §4.1, p.9

import Mathlib

namespace TSDRiem

/-- Orthogonal decomposition: the orthogonal projections `{P′_k}_{k∈[m]}` onto the subspaces
`K k` form an orthogonal decomposition of the inner product space `V` if
`Im(P′_i) ⊥ Im(P′_j)` for `j ≠ i` and `Span(⋃_{k∈[m]} Im(P′_k)) = V`.

Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, §4.1, p.9.

Formalization Note: the projections are recorded by their images `K k`; the projection itself
is `(K k).starProjection`. The printed "Im(P_j)" is read as Im(P′_j). `[m] = {1, …, m}` is
`Fin m`. -/
def IsOrthDecomp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {m : ℕ}
    (K : Fin m → Submodule ℝ V) : Prop :=
  (∀ i j, i ≠ j → K i ⟂ K j) ∧ ⨆ k, K k = ⊤

end TSDRiem


