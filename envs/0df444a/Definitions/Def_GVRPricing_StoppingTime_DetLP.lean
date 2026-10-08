-- Prove2me | Definitions.Def_GVRPricing_StoppingTime_DetLP
-- name    : GVRPricing_StoppingTime_DetLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T12:26:08.992968+00:00
-- url     : https://prove2.me/theorems/848c14ac-7f3b-448d-bddb-7fec88891751
-- title:
--   §4.0.1 — the deterministic problem as a linear program in the times $t_k$ spent at each price; $J^D(n,t)$ is its value
-- statement:
--   Let $t_k\ge 0$ be the amount of time the price is $p_k$ during the horizon $[0,t]$. With deterministic demand the deterministic pricing problem (11) becomes the linear program
--
--   $$J^D(n,t)=\sup\Big\{\sum_{k=1}^K r_k t_k \;:\; t_k\ge 0,\ \sum_{k=1}^K t_k\le t,\ \sum_{k=1}^K \lambda_k t_k\le n\Big\}.$$
--
--   The remaining time $t-\sum_k t_k$ is spent at the null price. An allocation $(t_k)$ **solves the LP** if it is feasible and no feasible allocation earns more. The file also defines the two-price allocation of Proposition 4: for an index $k$ with $1\le k\le K-1$,
--
--   $$t_k=\frac{n-\lambda_{k+1}t}{\lambda_k-\lambda_{k+1}},\qquad t_{k+1}=\frac{\lambda_k t-n}{\lambda_k-\lambda_{k+1}},\qquad t_j=0\ (j\notin\{k,k+1\}).$$
--
--   $J^D$ is the benchmark of Theorem 5: the ST heuristic's expected revenue is compared with it.
--
--   **Formalization Note** $J^D$ is defined directly as the value of the LP, the object Proposition 4 and Theorem 5 use; the reduction from the rate-path problem (11) by the occupation-time substitution is asserted on p. 1010 and is not formalized. For $n\ge 0$ and $t\ge 0$ the feasible set is nonempty ($t_k=0$) and its revenues are bounded by $t\max_k r_k$, so the real supremum is the LP optimum. Indices are 0-based in Lean.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1010 (PDF 12), §4.0.1 and Proposition 4

import Mathlib
import Definitions.Def_GVRPricing_StoppingTime_Menu

namespace GVRPricing.StoppingTime

variable {K : ℕ}

/-- Feasible time allocations of the deterministic problem (§4.0.1, p. 1010): `τ k ≥ 0` is the time
spent at price `p_k`, the total time is at most the horizon `t` (the rest is spent at the null
price `p_∞`, rate 0), and the deterministic sales `∑ λ_k τ_k` do not exceed the stock `n`. -/
def Feasible (M : Menu K) (n t : ℝ) (τ : Fin K → ℝ) : Prop :=
  (∀ k, 0 ≤ τ k) ∧ ∑ k, τ k ≤ t ∧ ∑ k, M.lam k * τ k ≤ n

/-- Revenue `∑ r_k τ_k` of a time allocation. -/
def lpRevenue (M : Menu K) (τ : Fin K → ℝ) : ℝ := ∑ k, M.r k * τ k

/-- The deterministic revenue `J^D(n, t)` for the discrete menu: the value of the linear program
of §4.0.1.  For `n ≥ 0`, `t ≥ 0` the set is nonempty (`τ = 0`) and bounded above by `t · max r`,
so this real `sSup` is the LP optimum (not a junk value). -/
noncomputable def detValue (M : Menu K) (n t : ℝ) : ℝ :=
  sSup (lpRevenue M '' {τ | Feasible M n t τ})

/-- `τ` solves the LP: it is feasible and no feasible allocation earns more. -/
def IsLPSolution (M : Menu K) (n t : ℝ) (τ : Fin K → ℝ) : Prop :=
  Feasible M n t τ ∧ ∀ τ', Feasible M n t τ' → lpRevenue M τ' ≤ lpRevenue M τ

/-- Proposition 4's allocation for the interior case with (0-based) `k* = k`:
`t_k = (n − λ_{k+1} t)/(λ_k − λ_{k+1})`, `t_{k+1} = (λ_k t − n)/(λ_k − λ_{k+1})`, all other `t_j = 0`. -/
noncomputable def twoPriceAlloc (M : Menu K) (k : ℕ) (n t : ℝ) : Fin K → ℝ := fun j =>
  if j.val = k then (n - M.lamN (k + 1) * t) / (M.lamN k - M.lamN (k + 1))
  else if j.val = k + 1 then (M.lamN k * t - n) / (M.lamN k - M.lamN (k + 1))
  else 0

end GVRPricing.StoppingTime


