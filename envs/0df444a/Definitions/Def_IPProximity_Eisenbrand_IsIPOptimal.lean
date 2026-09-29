-- Prove2me | Definitions.Def_IPProximity_Eisenbrand_IsIPOptimal
-- name    : IPProximity_Eisenbrand_IsIPOptimal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:29:57.088111+00:00
-- url     : https://prove2.me/theorems/3e200e10-c856-4f8d-b510-57ecb47157dd
-- title:
--   Optimal solution of the integer program (10)
-- statement:
--   An integer vector $z\in\mathbb Z^n$ is an optimal solution of the integer program (10) if it is feasible ($Az=b$, $0\le z\le u$) and
--   $$c^{T}z'\le c^{T}z\qquad\text{for every feasible integer solution } z'.$$
--   Problem (10) is a maximization problem.
-- source:
--   Eisenbrand & Weismantel, Proximity Results and Faster Algorithms for Integer Programming Using the Steinitz Lemma, ACM Trans. Algorithms 16(1), Article 5 (2019), p. 5:7, Eq. (10) and the sentence before Eq. (14)

import Mathlib
import Definitions.Def_IPProximity_Eisenbrand_ipFeasible

namespace IPProximity.Eisenbrand

/-- `z` is an optimal solution of the integer program (10)
`max {cᵀz : A z = b, 0 ≤ z ≤ u, z ∈ ℤⁿ}` (a maximization). -/
def IsIPOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Fin n → ℤ)
    (u : Fin n → ℕ) (z : Fin n → ℤ) : Prop :=
  z ∈ ipFeasible A b u ∧ ∀ z' ∈ ipFeasible A b u, dotProduct c z' ≤ dotProduct c z

end IPProximity.Eisenbrand


