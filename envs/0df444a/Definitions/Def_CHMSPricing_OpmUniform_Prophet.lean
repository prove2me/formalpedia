-- Prove2me | Definitions.Def_CHMSPricing_OpmUniform_Prophet
-- name    : CHMSPricing_OpmUniform_Prophet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:15:25.581602+00:00
-- url     : https://prove2.me/theorems/388fce61-b5e9-40e7-8bde-1608a79790c1
-- title:
--   Order statistics and the k-choice threshold stopping rule $t_i(c)$
-- statement:
--   Let $x_1, \dots, x_n$ be real numbers (a realisation of random variables $X_1, \dots, X_n$). The **order statistics** $x_{(1)} \ge x_{(2)} \ge \dots \ge x_{(n)}$ are the values sorted in non-increasing order, counted with multiplicity; $x_{(1)}$ is the maximum.
--
--   Fix $k \le n$ and a threshold $c$. The **threshold stopping rule** with threshold $c$ selects $k$ indices $t_1(c), \dots, t_k(c)$: $t_i(c)$ is the lesser of $n - k + i$ and the $i$-th smallest index $j$ with $x_j \ge c$, or simply $n - k + i$ when fewer than $i$ indices satisfy $x_j \ge c$:
--   $$t_i(c) = \min\big(n - k + i,\ j_i\big), \qquad j_i = \text{the } i\text{-th smallest } j \text{ with } x_j \ge c .$$
--   A gambler who inspects $x_1, x_2, \dots$ in order and must keep $k$ of them takes every value reaching $c$ while picks remain, and is forced to take the last values once the remaining samples are just enough to fill the $k$ picks.
--
--   These are the objects of the $k$-choice prophet inequality (Theorem 24), which compares the gambler's total $\sum_i X_{t_i(c)}$ with the prophet's $\sum_{i \le k} X_{(i)}$.
--
--   **Formalization Note** Indices are 0-based in Lean: `orderStat x i` is $x_{(i+1)}$ (so `orderStat x 0` is the maximum; out of range it is $0$), and for `i : Fin k`, `threshIdx hk x c i` is $t_{i+1}(c)$, the lesser of the 0-based index $n-k+i$ and the $(i+1)$-th smallest 0-based index $j$ with $x_j \ge c$. The proof `hk : k ≤ n` makes $n-k+i$ a valid index.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 18, App. D.2 (order statistics, (x)⁺, t_i(c))

import Mathlib

namespace CHMSPricing.OpmUniform

/-- Order statistics (App. D.2, p. 18), 0-based: `orderStat x i` is the `(i+1)`-th largest of
the values `x 0, …, x (n-1)`, counted with multiplicity (`orderStat x 0` is the maximum, i.e.
the paper's `X₍₁₎`). Out of range (`i ≥ n`) it is `0`. -/
noncomputable def orderStat {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ :=
  ((Finset.univ.val.map x).sort (fun a b => b ≤ a)).getD i 0

open Classical in
/-- The threshold stopping rule (App. D.2, p. 18), 0-based: for `i : Fin k` (with `k ≤ n`),
`threshIdx hk x c i` is the lesser of the index `n − k + i` and the `(i+1)`-th smallest index
`j` with `x j ≥ c`, or simply `n − k + i` when fewer than `i + 1` indices reach `c`. This is the
paper's `t_{i+1}(c)`. -/
noncomputable def threshIdx {n k : ℕ} (hk : k ≤ n) (x : Fin n → ℝ) (c : ℝ) (i : Fin k) :
    Fin n :=
  let forced : Fin n := ⟨n - k + i, by omega⟩
  match ((Finset.univ.filter (fun j => c ≤ x j)).sort (· ≤ ·))[(i : ℕ)]? with
  | some j => min forced j
  | none => forced

end CHMSPricing.OpmUniform


