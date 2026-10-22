-- Prove2me | Definitions.Def_LostSalesBaseStock_Convexity_dynamics
-- name    : LostSalesBaseStock_Convexity_dynamics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T04:41:15.009264+00:00
-- url     : https://prove2.me/theorems/232f24ee-56d7-410f-82b1-2555218ada43
-- title:
--   Base-stock lost-sales dynamics: orders $q_n$, on-hand $x_n$, sales $y_n$, $i_n$, $\pi_n$, lost sales $l_n$
-- statement:
--   Fix an arrival-index path $\lambda = (\lambda_n)_{n \ge 0}$ (with $\lambda_n \le n$ in the intended uses), a demand path $D = (D_n)_{n \ge 0}$ and a base-stock (order-up-to) level $S$. An order-up-to-$S$ policy is followed, starting with $S$ units on hand and nothing on order. In each period $n$ the following quantities are defined:
--
--   1. the order $q_n(S)$ placed in period $n$, with $q_0(S) = 0$ and $q_{n+1}(S) = y_n(S)$ (the order replaces the period's sales);
--   2. the inventory on hand after receiving period $n$'s shipments, $x_n(S) = S - \sum_{\lambda_n < t \le n} q_t(S)$;
--   3. the sales $y_n(S) = \min(x_n(S), D_n)$;
--   4. the end-of-period inventory on hand $i_n(S) = x_n(S) - y_n(S)$;
--   5. the end-of-period inventory position $\pi_n(S) = S - y_n(S)$;
--   6. the lost sales $l_n(S) = D_n - y_n(S)$.
--
--   Equivalently, the orders satisfy the recursion
--
--   $$
--   q_0(S) = 0, \qquad q_{n+1}(S) = \min\Big(S - \sum_{\lambda_n < t \le n} q_t(S),\; D_n\Big),
--   $$
--
--   which is well founded because every index $t$ in the sum satisfies $t \le n$. With $\lambda_0 = 0$ the sum for $x_0$ is empty and $x_0(S) = S$.
--
--   One set of dynamics serves both lead-time models of the paper: the sample-path results use the arrival index of a lead-time path $L$, the Kaplan-model results use the Kaplan index of $\rho$.
--
--   **Formalization Note** The recursion is written for the orders (`orderQty`); `onHand`, `sales`, `endOnHand`, `invPosition` and `lostSales` are defined from it. The file also contains two structural lemmas, $q_0 = 0$ and $q_{n+1} = y_n$. All quantities are real-valued and defined for every real $S$; the theorems restrict to $S \ge 0$.
-- source:
--   Janakiraman and Roundy, Lost-Sales Problems with Stochastic Lead Times: Convexity Results for Base-Stock Policies, Oper. Res. 52(5) (2004), p. 797, Section 3 (x_n, y_n, i_n, pi_n, l_n, q_{n+1} = y_n, x_0 = S, q_0 = 0); p. 798, Eqs. (4.3)-(4.6)

import Mathlib

namespace LostSalesBaseStock.Convexity

/-- Order sizes `q_n(S)` of the order-up-to-`S` lost-sales system (Janakiraman–Roundy 2004, §3,
p. 797, and (4.3), p. 798), for an arrival-index path `lam` (`lam n = λ_n`), a demand path `D`
and a base-stock level `S`. The system starts with `S` on hand and nothing on order, so
`q_0 = 0`, and the order placed in period `n + 1` replaces period `n`'s sales:
`q_{n+1} = y_n = min(x_n, D_n)` with `x_n = S − ∑_{λ_n < t ≤ n} q_t`. The recursion is
well founded because every `t` in `(λ_n, n]` satisfies `t ≤ n < n + 1`. -/
noncomputable def orderQty (lam : ℕ → ℕ) (D : ℕ → ℝ) (S : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
    min (S - ∑ t ∈ (Finset.Ioc (lam n) n).attach, orderQty lam D S t.1) (D n)
termination_by n => n
decreasing_by
  have := (Finset.mem_Ioc.mp t.2).2
  omega

/-- On-hand inventory `x_n(S) = S − ∑_{λ_n < t ≤ n} q_t(S)` after receiving the shipments that
arrive in period `n` (p. 797; (4.3)). With `λ_0 = 0` this gives `x_0 = S`. -/
noncomputable def onHand (lam : ℕ → ℕ) (D : ℕ → ℝ) (S : ℝ) (n : ℕ) : ℝ :=
  S - ∑ t ∈ Finset.Ioc (lam n) n, orderQty lam D S t

/-- Sales `y_n(S) = min(x_n(S), D_n)` in period `n` (p. 797). -/
noncomputable def sales (lam : ℕ → ℕ) (D : ℕ → ℝ) (S : ℝ) (n : ℕ) : ℝ :=
  min (onHand lam D S n) (D n)

/-- End-of-period inventory on hand `i_n(S) = x_n(S) − y_n(S)` (p. 797; (4.4)). -/
noncomputable def endOnHand (lam : ℕ → ℕ) (D : ℕ → ℝ) (S : ℝ) (n : ℕ) : ℝ :=
  onHand lam D S n - sales lam D S n

/-- End-of-period inventory position `π_n(S) = S − y_n(S)` (p. 797; (4.5)). -/
noncomputable def invPosition (lam : ℕ → ℕ) (D : ℕ → ℝ) (S : ℝ) (n : ℕ) : ℝ :=
  S - sales lam D S n

/-- Lost sales `l_n(S) = D_n − y_n(S)` in period `n` (p. 797; (4.6)). -/
noncomputable def lostSales (lam : ℕ → ℕ) (D : ℕ → ℝ) (S : ℝ) (n : ℕ) : ℝ :=
  D n - sales lam D S n

/-- Structural: `q_0(S) = 0`. -/
theorem orderQty_zero (lam : ℕ → ℕ) (D : ℕ → ℝ) (S : ℝ) : orderQty lam D S 0 = 0 := by
  rw [orderQty]

/-- Structural: `q_{n+1}(S) = y_n(S)` (p. 797: "the amount ordered in period `n + 1` is given
by `q_{n+1} = y_n`"). -/
theorem orderQty_succ (lam : ℕ → ℕ) (D : ℕ → ℝ) (S : ℝ) (n : ℕ) :
    orderQty lam D S (n + 1) = sales lam D S n := by
  rw [orderQty, sales, onHand, Finset.sum_attach (Finset.Ioc (lam n) n)
    (fun t => orderQty lam D S t)]

end LostSalesBaseStock.Convexity


