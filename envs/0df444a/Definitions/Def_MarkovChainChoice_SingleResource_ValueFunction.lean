-- Prove2me | Definitions.Def_MarkovChainChoice_SingleResource_ValueFunction
-- name    : MarkovChainChoice_SingleResource_ValueFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:15:25.311102+00:00
-- url     : https://prove2.me/theorems/8e97a452-56d3-4678-975d-ddcc0aa1fee7
-- title:
--   The (Single Resource) dynamic program: value functions $V_t(x)$, marginal values $\Delta V_t(x)$ and the stage objective
-- statement:
--   A single resource with $c$ units of capacity is sold over $T$ time periods. In each period at most one customer arrives and chooses among the offered products according to the Markov chain choice model; a sale of product $j$ earns $r_j$ and consumes one unit. Let $V_t(x)$ be the optimal total expected revenue over periods $t,\dots,T$ with $x$ units of remaining capacity at the beginning of period $t$. It is computed by the **(Single Resource)** dynamic program
--   $$V_t(x)=\max_{S\subseteq N}\Big\{\sum_{j\in N}P_{j,S}\{r_j+V_{t+1}(x-1)-V_{t+1}(x)\}\Big\}+V_{t+1}(x),$$
--   for $t=1,\dots,T$ and $x\ge 1$, with boundary conditions $V_{T+1}(x)=0$ for all $x$ and $V_t(0)=0$ for all $t$.
--
--   Write $\Delta V_t(x)=V_t(x)-V_t(x-1)$ for the marginal value of capacity, and
--   $$\sum_{j\in N}P_{j,S}\{r_j+V_{t+1}(x-1)-V_{t+1}(x)\}$$
--   for the objective of the problem on the right side of the dynamic program; an optimal subset $\hat S_t(x)$ maximizes it over $S\subseteq N$.
--
--   These objects are the subject of Theorem 5, which describes how the optimal offer sets change with the remaining capacity and the remaining time.
--
--   **Formalization Note** The recursion is written on the number $k$ of periods to go (`valueToGo M r k x`), so that no natural-number subtraction appears in the recursion, and `value M r T t x` $=V_t(x)$ is `valueToGo M r (T+1-t) x`; it is the paper's $V_t(x)$ for $1\le t\le T+1$, and statements only use it in that range. The maximum over $S\subseteq N$ is `Finset.sup'` over the finite, nonempty family of all subsets, hence attained. Capacities $x$ are not truncated at $c$: the value for $x\le c$ only depends on smaller capacities, so this agrees with the paper on $x=0,\dots,c$. `deltaValue M r T t x` $=\Delta V_t(x)$ and `stageObj M r T t x S` is the stage objective above; both are only used for $x\ge1$.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, pp. 1328–1329, Section 5, (Single Resource), and p. 1329 (definition of Ŝ_t(x) and ΔV_t(x))

import Mathlib
import Definitions.Def_MarkovChainChoice_Shared_Balance
open MarkovChainChoice.Shared

namespace MarkovChainChoice.SingleResource

variable {n : ℕ}

/-- The (Single Resource) value function indexed by the number `k` of periods to go:
`valueToGo M r 0 x = 0`, `valueToGo M r (k+1) 0 = 0`, and
`valueToGo M r (k+1) (x+1) = max_{S ⊆ N} Σ_j P_{j,S} (r_j + W_k(x) − W_k(x+1)) + W_k(x+1)`,
Feldman–Topaloglu 2017, pp. 1328–1329. -/
noncomputable def valueToGo (M : Model n) (r : Fin n → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | k + 1, x + 1 =>
      (Finset.univ : Finset (Finset (Fin n))).sup' Finset.univ_nonempty
          (fun S => ∑ j, purchase M S j * (r j + valueToGo M r k x - valueToGo M r k (x + 1))) +
        valueToGo M r k (x + 1)

/-- `value M r T t x = V_t(x)` for the horizon `T`, meaningful for `1 ≤ t ≤ T + 1`:
`V_t = valueToGo (T + 1 − t)`, so `V_{T+1} = 0`. -/
noncomputable def value (M : Model n) (r : Fin n → ℝ) (T t x : ℕ) : ℝ :=
  valueToGo M r (T + 1 - t) x

/-- The marginal value `ΔV_t(x) = V_t(x) − V_t(x − 1)` (used for `x ≥ 1`). -/
noncomputable def deltaValue (M : Model n) (r : Fin n → ℝ) (T t x : ℕ) : ℝ :=
  value M r T t x - value M r T t (x - 1)

/-- The objective `Σ_{j∈N} P_{j,S} {r_j + V_{t+1}(x − 1) − V_{t+1}(x)}` of the problem on the right
side of (Single Resource) in period `t` with `x ≥ 1` units of capacity (p. 1329). -/
noncomputable def stageObj (M : Model n) (r : Fin n → ℝ) (T t x : ℕ) (S : Finset (Fin n)) : ℝ :=
  ∑ j, purchase M S j * (r j + value M r T (t + 1) (x - 1) - value M r T (t + 1) x)

end MarkovChainChoice.SingleResource


