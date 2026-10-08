-- Prove2me | Definitions.Def_LawlerMoore_WeightedTardy_PrefixFeasible
-- name    : LawlerMoore_WeightedTardy_PrefixFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T13:07:25.433692+00:00
-- url     : https://prove2.me/theorems/244a96b0-e6cd-4c08-aafb-f444fc772838
-- title:
--   Section 6 — the prefix-constrained knapsack: constraints and objective
-- statement:
--   Let $n$ jobs have nonnegative integer processing times $a'_1, \dots, a'_n$, nonnegative integer deadlines $d_1, \dots, d_n$ and real weights $p_1, \dots, p_n$. A 0–1 vector $x = (x_1, \dots, x_n)$, where $x_j = 1$ if job $j$ is to be on time and $x_j = 0$ if job $j$ is to be tardy, is **prefix-feasible** if
--   $$
--   a'_1 x_1 + a'_2 x_2 + \cdots + a'_k x_k \le d_k \qquad (k = 1, 2, \dots, n).
--   $$
--   Its **value** is $\sum_{j=1}^n p_j x_j$.
--
--   These are the constraints and the objective of the knapsack-type problem of Section 6 of Lawler and Moore, "Maximize $\sum p_j x_j$ subject to" the $n$ nested prefix constraints, to which the weighted-tardy-jobs problem of Section 5 is shown to be equivalent.
--
--   **Formalization Note** `x : Fin n → Bool`, with `true` for $x_j = 1$; `PrefixFeasible a' d x` sums over Lean indices $i \le k$ in $\mathbb N$; `knapValue p x` is $\sum_j p_j x_j$ in $\mathbb R$. Lean job $i$ is the paper's job $i + 1$.
-- source:
--   Lawler, Moore, A Functional Equation and Its Application to Resource Allocation and Sequencing Problems, Management Sci. 16 (1969), p. 80, Section 6

import Mathlib

namespace LawlerMoore.WeightedTardy

/-- The constraints of the prefix-constrained knapsack problem of §6 (Lawler–Moore 1969, p. 80):
the 0–1 vector `x` (`x j = true` means `x_j = 1`, job `j` on time; `x j = false` means
`x_j = 0`, job `j` tardy) satisfies
`a'_1 x_1 + ⋯ + a'_k x_k ≤ d_k` for every `k = 1, …, n`.
Lean job `i` is the paper's job `i + 1`, so the `k`-th constraint sums over `i ≤ k`. -/
def PrefixFeasible {n : ℕ} (a' d : Fin n → ℕ) (x : Fin n → Bool) : Prop :=
  ∀ k : Fin n, ∑ i ∈ Finset.univ.filter (fun i => i ≤ k), a' i * (x i).toNat ≤ d k

/-- The objective `∑_{j=1}^n p_j x_j` of the knapsack problems of §6 (p. 80). -/
noncomputable def knapValue {n : ℕ} (p : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ j, p j * ((x j).toNat : ℝ)

end LawlerMoore.WeightedTardy


