-- Prove2me | Definitions.Def_OmniThreshold_IsFeasible
-- name    : OmniThreshold_IsFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:33:57.805557+00:00
-- url     : https://prove2.me/theorems/f657b83e-5d36-4338-a6f4-f94fb29db103
-- title:
--   Constraints of the second-stage problem, LP (1) and LP (2)
-- statement:
--   There are $n$ locations. Location $i$ holds inventory $\mathcal I_i\in\mathbb N$, has in-store demand $\mathcal D_i^P\in\mathbb N$, and has accepted $A_i^O\in\mathbb N$ online orders. A decision $(C,R,F)$ with $C,R\in\mathbb R^n$ and $F\in\mathbb R^{n\times n}$ is **feasible** for the second-stage problem if
--   $$
--   \min(\mathcal D_i^P,\mathcal I_i)+R_i+\sum_{j=1}^nF_{ij}=\mathcal I_i,\qquad
--   C_i+\sum_{j=1}^nF_{ji}=A_i^O\qquad(i\in[n]),
--   $$
--   and $C_i,R_i,F_{ij}\ge0$ for all $i,j$. Here $C_i$ counts the accepted orders at $i$ that are cancelled, $R_i$ is the inventory left over at $i$, and $F_{ij}$ counts the online orders received at $j$ and filled from the inventory at $i$.
--
--   The two constraint families say that all inventory at a location serves in-store demand, is saved, or fills online orders, and that every accepted order is either cancelled or filled. LP (1) and LP (2) share these constraints.
--
--   **Formalization Note** Locations are `Fin n`. Data in $\mathbb N$ are cast to $\mathbb R$. The decision variables are real, as in a linear program; integrality of LP (1) (Proposition 4) is a separate result.
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, LP (1), p.3 and its description p.4; LP (2), p.9

import Mathlib

namespace OmniThreshold

/-- The **constraints of the second-stage problem**, LP (1) and LP (2) (Jia, Karp, Ravi & Tayur,
*Effective Online Order Acceptance Policies for Omni-Channel Fulfillment*, SSRN 3932692, LP (1),
p.3, and LP (2), p.9; both have the same constraints):
`min(D_i^P, I_i) + R_i + ∑_j F_ij = I_i` and `C_i + ∑_j F_ji = A_i^O` for every location `i`, and
`C_i, R_i, F_ij ≥ 0`.

Here `I i` is the inventory at location `i`, `DP i` its in-store demand and `A i` the number of
online orders accepted at `i`; the decision is `x = (C, R, F)`, where `C i` is the number of
orders at `i` cancelled, `R i` the inventory left over at `i`, and `F i j` the number of online
orders received at `j` and filled from the inventory at `i` (p.3; equivalently, p.4, `F j i` is
the number filled from `j` and shipped to customers at `i`).

**Formalization Note** The `n` locations are `Fin n`. Inventories, demands and accepted orders are
natural numbers, cast to `ℝ`; the decision variables are real, as in the LP (the integrality of
LP (1), Proposition 4, is a separate result). -/
def IsFeasible {n : ℕ} (I DP A : Fin n → ℕ)
    (x : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → Fin n → ℝ)) : Prop :=
  (∀ i, min (DP i : ℝ) (I i : ℝ) + x.2.1 i + ∑ j, x.2.2 i j = (I i : ℝ)) ∧
  (∀ i, x.1 i + ∑ j, x.2.2 j i = (A i : ℝ)) ∧
  (∀ i, 0 ≤ x.1 i) ∧ (∀ i, 0 ≤ x.2.1 i) ∧ (∀ i j, 0 ≤ x.2.2 i j)

end OmniThreshold


