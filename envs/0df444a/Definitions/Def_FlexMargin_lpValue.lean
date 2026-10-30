-- Prove2me | Definitions.Def_FlexMargin_lpValue
-- name    : FlexMargin_lpValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:33:12.911634+00:00
-- url     : https://prove2.me/theorems/39828aeb-b6e9-42c4-ac32-7c728cfc6589
-- title:
--   Maximum profit $g(\mathcal A, d)$, the LP (1)
-- statement:
--   For a system with $m$ plants of capacities $C_1,\dots,C_m$ and $n$ products with margins $p_1,\dots,p_n$, a **flexibility design** $\mathcal A$ is a set of arcs $(a_j,b_i)$ meaning that plant $j$ can produce product $i$. For a demand vector $d$, the **maximum profit** is
--
--   $$
--   g(\mathcal A,d)=\max\Big\{\sum_{(a_j,b_i)\in\mathcal A}p_i x_{ij}\;:\;\sum_{j=1}^m x_{ij}\le d_i\ \forall i,\ \sum_{i=1}^n x_{ij}\le C_j\ \forall j,\ x\ge 0\Big\}.
--   $$
--
--   This is the linear program (1), the deterministic performance of a design on which all robust measures of the paper are built.
--
--   **Formalization Note** The value is the supremum of the feasible objective values. For $d\ge0$ and $C\ge0$ the feasible set contains $x=0$ and is bounded, so the supremum is the maximum; every statement uses it under these conditions.
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §2, display (1), pp. 11–12

import Mathlib

open Finset

namespace FlexMargin

/-- **Maximum profit `g(𝒜, d)` of a flexibility design, the LP (1).**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §2, display (1), pp. 11–12:
"g(A,d) = max Σ_{(aj,bi)∈A} pi xij s.t. Σ_{j=1}^m xij ≤ di, ∀1 ≤ i ≤ n, Σ_{i=1}^n xij ≤ Cj,
∀1 ≤ j ≤ m, xij ≥ 0, ∀1 ≤ i ≤ n, 1 ≤ j ≤ m."

Plants are `Fin m` (capacities `C`), products are `Fin n` (margins `p`, demands `d`). A design
`A` is a set of (plant, product) arcs, the paper's `(a_j, b_i)`. A production plan
`x : Fin m × Fin n → ℝ` assigns to (plant `j`, product `i`) the paper's `x_ij`.
`lpValue C p A d` is the supremum of the profit `Σ_{(j,i) ∈ A} p_i x_(j,i)` over all
nonnegative plans meeting the demand and capacity constraints.

**Formalization Note.** As printed, the constraints sum over all plants (resp. products), and
only the objective is restricted to arcs of `A`. For `d ≥ 0` and `C ≥ 0` the feasible set
contains `x = 0` and is bounded, so the supremum is the paper's maximum; every statement using
`lpValue` assumes `0 ≤ C` and nonnegative demands (the paper's `d ∈ ℝ^n_+`). For a demand
vector with a negative entry the set is empty and `sSup ∅ = 0` is a junk value, never used.
In the paper's general system the margins are `p_i = P_{t}` for the category `t` of product
`i`; here the margin vector `p` is passed directly. -/
noncomputable def lpValue {m n : ℕ} (C : Fin m → ℝ) (p : Fin n → ℝ)
    (A : Finset (Fin m × Fin n)) (d : Fin n → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ x : Fin m × Fin n → ℝ, (∀ a, 0 ≤ x a) ∧
      (∀ i, ∑ j, x (j, i) ≤ d i) ∧ (∀ j, ∑ i, x (j, i) ≤ C j) ∧
      v = ∑ a ∈ A, p a.2 * x a}

end FlexMargin


