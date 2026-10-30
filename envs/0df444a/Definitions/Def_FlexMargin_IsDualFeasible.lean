-- Prove2me | Definitions.Def_FlexMargin_IsDualFeasible
-- name    : FlexMargin_IsDualFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:33:30.338888+00:00
-- url     : https://prove2.me/theorems/f3e0bacd-f07b-4f51-9486-62c944902c25
-- title:
--   Feasibility for the dual problem (3)
-- statement:
--   Given margins $p$ and a design $\mathcal A$, product prices $y\in\mathbb R^n$ and plant prices $z\in\mathbb R^m$ are **feasible for the dual problem (3)** if
--
--   $$
--   y_i+z_j\ge p_i\ \ \forall (a_j,b_i)\in\mathcal A,\qquad y_i\ge0\ \ \forall i,\qquad z_j\ge0\ \ \forall j .
--   $$
--
--   The dual objective is $\sum_i d_i y_i+\sum_j C_j z_j$; by strong duality its minimum over feasible $(y,z)$ is $g(\mathcal A,d)$.
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §3.1, display (3), p. 16

import Mathlib

namespace FlexMargin

/-- **Feasibility for the dual problem (3).**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §3.1, display (3), p. 16:
"g(A,d) = min_{y,z} Σ_{i=1}^n di yi + Σ_{j=1}^m Cj zj s.t. yi + zj ≥ pi, ∀(aj,bi) ∈ A,
yi ≥ 0, ∀1 ≤ i ≤ n, zj ≥ 0, ∀1 ≤ j ≤ m".

`IsDualFeasible p A y z` says that the product prices `y : Fin n → ℝ` and plant prices
`z : Fin m → ℝ` satisfy the three constraint families of (3) for the design `A` (arcs are
(plant, product) pairs) and the margins `p`. The objective `Σ_i d_i y_i + Σ_j C_j z_j` is written
out in each statement that uses it.

**Formalization Note.** Feasibility does not involve `d` or `C`; nothing is added. -/
def IsDualFeasible {m n : ℕ} (p : Fin n → ℝ) (A : Finset (Fin m × Fin n))
    (y : Fin n → ℝ) (z : Fin m → ℝ) : Prop :=
  (∀ a ∈ A, p a.2 ≤ y a.2 + z a.1) ∧ (∀ i, 0 ≤ y i) ∧ ∀ j, 0 ≤ z j

end FlexMargin


