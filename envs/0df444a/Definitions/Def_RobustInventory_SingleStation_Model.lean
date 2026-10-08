-- Prove2me | Definitions.Def_RobustInventory_SingleStation_Model
-- name    : RobustInventory_SingleStation_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:48:53.097993+00:00
-- url     : https://prove2.me/theorems/8066cd5d-0087-4ebf-81cc-951d3b56b126
-- title:
--   §3.1, Eqs. (5)–(8) — the single-station model: horizon $T$, stock $x_0$, demands $\bar w,\hat w$, budgets $\Gamma$, costs $c,K,h,p$
-- statement:
--   This file fixes the single-station inventory model of Bertsimas and Thiele, §3.1.
--
--   A single item is ordered at a single installation over periods $k = 0,\dots,T-1$. The data are an initial stock $x_0 \in \mathbb R$; for each period a **nominal demand** $\bar w_k$ and a **maximal deviation** $\hat w_k \ge 0$, so that the demand $w_k$ ranges over $[\bar w_k - \hat w_k, \bar w_k + \hat w_k]$; **budgets of uncertainty** $\Gamma_k$ with
--   $$0 \le \Gamma_0,\qquad \Gamma_k \le \Gamma_{k+1} \le \Gamma_k + 1 \quad (k \ge 0);$$
--   a unit ordering cost $c > 0$, a fixed ordering cost $K \ge 0$, a unit holding cost $h \ge 0$ and a unit shortage cost $p > c$.
--
--   With orders $u_k$ and demands $w_k$, excess demand is backlogged and the stock at the end of period $k$ is (Eqs. (5)–(6))
--   $$x_{k+1} = x_0 + \sum_{i=0}^{k} (u_i - w_i).$$
--   The purchasing cost (7) is $C(u) = K + c\,u$ if $u > 0$ and $C(0) = 0$, and the holding/shortage cost (8) is $R(x) = \max(hx, -px)$. For a fixed demand sequence $w$ the **nominal cost** of an order sequence $u$ is
--   $$\sum_{k=0}^{T-1} \big( C(u_k) + R(x_{k+1}) \big),$$
--   and $u$ is **optimal for the nominal problem with demand $w$** if $u_k \ge 0$ for $k < T$ and $u$ minimizes this cost over all order sequences that are nonnegative on the horizon. The nominal stock is $\bar x_{k+1} = x_0 + \sum_{i=0}^{k}(u_i - \bar w_i)$.
--
--   Finally, the **order-up-to** (base-stock) policy of Definition 3.1 with thresholds $S_k$ (and $s_k = S_k$, i.e. without fixed cost), run against a demand sequence $w$ from $x_0$, orders $u_k = \max(S_k - x_k, 0)$ at the beginning of period $k$, so that $x_{k+1} = \max(x_k, S_k) - w_k$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Sequences are `ℕ → ℝ`; only the values at $k < T$ matter. `stock w u k` is $x_{k+1}$ (the stock at the *end* of period $k$), so `xbar u k` is $\bar x_{k+1}$. The fixed cost is written with the indicator $C$ instead of the binary variables $v_k$ and the big-$M$ constraint $0 \le u_k \le M v_k$ of (12); for fixed $u$ the two give the same optimal value when $M \ge \max_k u_k$, and the page's "$M$ is a large positive number" is not a fixed constant. The paper's nonnegativity of demand ($\bar w_k - \hat w_k \ge 0$) is not part of the model: no statement of the mission needs it, and where a nonnegative demand is needed it is a hypothesis of that statement. $p \ge 0$ follows from $p > c > 0$.
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), pp. 152–153 (PDF 3–4), §3.1, Eqs. (5)–(12) and the standing assumptions; p. 154 (PDF 5), Definition 3.1

import Mathlib

namespace RobustInventory.SingleStation

open Finset

/-- The data of the single-station inventory model of Bertsimas and Thiele (2006), §3.1,
pp. 152–153, with the standing assumptions of that section.

* `T`: the horizon; periods are `k = 0, …, T - 1`;
* `x0`: the initial stock `x₀`;
* `wbar k`, `what k`: the nominal demand `w̄_k` and the maximal deviation `ŵ_k ≥ 0` of period `k`;
  the demand `w_k` lies in `[w̄_k - ŵ_k, w̄_k + ŵ_k]`;
* `Γ k`: the budget of uncertainty `Γ_k` of period `k`, nonnegative, nondecreasing in `k`,
  and increasing by at most `1` per period;
* `c > 0`, `K ≥ 0`: unit and fixed ordering cost, eq. (7);
* `h ≥ 0`, `p > c`: unit holding and shortage cost, eq. (8). -/
structure Model where
  T : ℕ
  x0 : ℝ
  wbar : ℕ → ℝ
  what : ℕ → ℝ
  Γ : ℕ → ℝ
  c : ℝ
  K : ℝ
  h : ℝ
  p : ℝ
  hc : 0 < c
  hK : 0 ≤ K
  hh : 0 ≤ h
  hpc : c < p
  hwhat : ∀ k, 0 ≤ what k
  hΓ0 : 0 ≤ Γ 0
  hΓmono : ∀ k, Γ k ≤ Γ (k + 1)
  hΓstep : ∀ k, Γ (k + 1) ≤ Γ k + 1

namespace Model

variable (M : Model)

/-- The purchasing cost (7): `C(u) = K + c·u` if `u > 0` and `C(u) = 0` otherwise
(orders are nonnegative, so "otherwise" is `u = 0` on the feasible set). -/
noncomputable def C (u : ℝ) : ℝ := if 0 < u then M.K + M.c * u else 0

/-- The holding/shortage cost (8): `R(x) = max(h x, -p x)`. -/
noncomputable def R (x : ℝ) : ℝ := max (M.h * x) (-(M.p * x))

/-- `stock w u k` is the stock `x_{k+1} = x₀ + ∑_{i=0}^{k} (u_i - w_i)` at the end of period `k`
(eq. (6)), for the demand sequence `w` and the order sequence `u`. -/
def stock (w u : ℕ → ℝ) (k : ℕ) : ℝ := M.x0 + ∑ i ∈ range (k + 1), (u i - w i)

/-- `xbar u k` is the nominal stock `x̄_{k+1} = x₀ + ∑_{i=0}^{k} (u_i - w̄_i)` (p. 153). -/
def xbar (u : ℕ → ℝ) (k : ℕ) : ℝ := M.stock M.wbar u k

/-- The cost of the nominal (deterministic) problem with demand sequence `w` and orders `u`:
`∑_{k=0}^{T-1} (C(u_k) + R(x_{k+1}))`, i.e. (9)–(12) with a fixed demand, the fixed cost being
written with the indicator `C` instead of binary variables and a big-`M` constraint. -/
noncomputable def nominalCost (w u : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range M.T, (M.C (u k) + M.R (M.stock w u k))

/-- `u` is an optimal order sequence of the nominal problem with demand `w`: it is nonnegative
on the horizon and minimizes `nominalCost w` over all nonnegative order sequences. -/
def IsNominalOptimal (w u : ℕ → ℝ) : Prop :=
  (∀ k < M.T, 0 ≤ u k) ∧
    ∀ u' : ℕ → ℝ, (∀ k < M.T, 0 ≤ u' k) → M.nominalCost w u ≤ M.nominalCost w u'

end Model

/-- The stock at the beginning of period `k` under the order-up-to (base-stock, Definition 3.1
with `s_k = S_k`) policy with thresholds `S`, initial stock `x0` and demand `w`:
`x_0 = x0` and `x_{k+1} = max(x_k, S_k) - w_k`. -/
def orderUpToStock (x0 : ℝ) (S w : ℕ → ℝ) : ℕ → ℝ
  | 0 => x0
  | k + 1 => max (orderUpToStock x0 S w k) (S k) - w k

/-- The orders of the order-up-to policy with thresholds `S` along its own trajectory:
`u_k = S_k - x_k` if `x_k < S_k` and `0` otherwise, i.e. `u_k = max(S_k - x_k, 0)`. -/
noncomputable def orderUpTo (x0 : ℝ) (S w : ℕ → ℝ) (k : ℕ) : ℝ :=
  max (S k - orderUpToStock x0 S w k) 0

end RobustInventory.SingleStation


