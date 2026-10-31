-- Prove2me | Definitions.Def_LPAllocRM_IsLPOptimal
-- name    : LPAllocRM_IsLPOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:59.83599+00:00
-- url     : https://prove2.me/theorems/5efc79da-e9ad-46f0-bfe7-ca7dbac8331b
-- title:
--   Optimal solutions of the bounded LP $\max\{f\cdot x : Ax\le b,\ 0\le x\le u\}$
-- statement:
--   A vector $x$ is an **optimal solution** of $\max_x\{f\cdot x : Ax\le b,\ 0\le x\le u\}$ if it is feasible and $f\cdot y\le f\cdot x$ for every feasible $y$.
--
--   The paper denotes by $x^*$ an optimal solution of (3), "In case of multiple optima, we choose among them in an arbitrary manner", and sets $\beta\equiv f\cdot x^*$. The theorems of this mission hold for every optimal solution.
--
--   **Formalization Note** Optimality is stated against every feasible point, so no optimal value needs to exist to define it.
-- source:
--   Cooper, Asymptotic Behavior of an Allocation Policy for Revenue Management, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855, eq. (3) and the sentence after it, p.723

import Mathlib
import Definitions.Def_LPAllocRM_LPFeasible
open Matrix

namespace LPAllocRM

/-- `x` is an optimal solution of `max {f · x : A x ≤ b, 0 ≤ x ≤ u}`: it is feasible and
`f · y ≤ f · x` for every feasible `y`.
Cooper, *Asymptotic Behavior of an Allocation Policy for Revenue Management*, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855,
LP (3) and "we will denote by x∗ an optimal solution", p.723 (PDF p.4); the kth LP (6), p.723.

**Formalization Note** Optimality is stated against every feasible point, so no optimal value
(supremum) is needed to define it. "In case of multiple optima, we choose among them in an
arbitrary manner" (p.723) is rendered by quantifying the theorems over every `x` with
`IsLPOptimal A c μ f x`. -/
def IsLPOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (u : Fin n → ℝ)
    (f : Fin n → ℝ) (x : Fin n → ℝ) : Prop :=
  LPFeasible A b u x ∧ ∀ y : Fin n → ℝ, LPFeasible A b u y → f ⬝ᵥ y ≤ f ⬝ᵥ x

end LPAllocRM


