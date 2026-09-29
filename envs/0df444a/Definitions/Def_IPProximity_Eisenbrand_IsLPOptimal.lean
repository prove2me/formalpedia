-- Prove2me | Definitions.Def_IPProximity_Eisenbrand_IsLPOptimal
-- name    : IPProximity_Eisenbrand_IsLPOptimal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:29:25.115053+00:00
-- url     : https://prove2.me/theorems/55fe6ddd-bcec-402c-95d3-10e5e934fb31
-- title:
--   Optimal solution of the LP relaxation of (10)
-- statement:
--   A point $x\in\mathbb R^n$ is an optimal solution of the LP relaxation of (10) if it is feasible, $x\in P(A,b,u)$, and
--   $$c^{T}y\le c^{T}x\qquad\text{for every } y\in P(A,b,u).$$
--   Problem (10) is a maximization problem, so optimal means maximal objective value.
--
--   **Formalization Note** The integral objective vector $c$ is cast to $\mathbb R$ and $c^Tx$ is `dotProduct`.
-- source:
--   Eisenbrand & Weismantel, Proximity Results and Faster Algorithms for Integer Programming Using the Steinitz Lemma, ACM Trans. Algorithms 16(1), Article 5 (2019), p. 5:7, Eq. (10) and the sentence before Eq. (14)

import Mathlib
import Definitions.Def_IPProximity_Eisenbrand_lpPolytope

namespace IPProximity.Eisenbrand

/-- `x` is an optimal solution of the linear programming relaxation
`max {cᵀx : A x = b, 0 ≤ x ≤ u, x ∈ ℝⁿ}` of the integer program (10) (a maximization). -/
def IsLPOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Fin n → ℤ)
    (u : Fin n → ℕ) (x : Fin n → ℝ) : Prop :=
  x ∈ lpPolytope A b u ∧
    ∀ y ∈ lpPolytope A b u, dotProduct (fun i => (c i : ℝ)) y ≤ dotProduct (fun i => (c i : ℝ)) x

end IPProximity.Eisenbrand


