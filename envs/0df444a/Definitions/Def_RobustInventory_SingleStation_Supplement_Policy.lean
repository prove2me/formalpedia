-- Prove2me | Definitions.Def_RobustInventory_SingleStation_Supplement_Policy
-- name    : RobustInventory_SingleStation_Supplement_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:21:51.247256+00:00
-- url     : https://prove2.me/theorems/d72012d9-7a68-441d-afef-26204d047b27
-- title:
--   Definition 3.1: the rule with thresholds $(s_k,S_k)$ and the nominal problem that remains from period $k$ and stock $x$
-- statement:
--   This file defines what it means for a threshold rule to be optimal at every period and every stock in the single-station inventory model, with horizon $T$, purchasing cost $C$ of (7) and holding/shortage cost $R$ of (8).
--
--   For a demand sequence $w$, a period $k$ and a stock $x$ at the beginning of period $k$, the **tail problem** is
--   $$\min_{u_k,\dots,u_{T-1}\ge0}\ \sum_{i=k}^{T-1}\Big[C(u_i)+R\Big(x+\sum_{l=k}^{i}(u_l-w_l)\Big)\Big].$$
--   An order sequence is optimal for it if it is nonnegative on periods $k,\dots,T-1$ and has least cost among all such sequences.
--
--   Given thresholds $(s_i,S_i)$, the **rule of Definition 3.1** orders, at stock $x_i$,
--   $$u_i=\begin{cases}S_i-x_i&\text{if }x_i<s_i,\\0&\text{otherwise,}\end{cases}\qquad x_{i+1}=x_i+u_i-w_i,$$
--   starting from $x_k=x$. At $k=0$ and $x=x_0$ the tail problem is the nominal problem of the published model.
--
--   **Formalization Note** The rule is started at an arbitrary pair $(k,x)$; its values at periods before $k$ are never used.
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), p. 154 (PDF 5), Definition 3.1; p. 152 (PDF 3), Eqs. (5)–(8)

import Definitions.Def_RobustInventory_SingleStation_Model

namespace RobustInventory.SingleStation.Supplement

open Finset

/-- The stock at the end of period `i ≥ k` when the stock at the beginning of period `k` is `x`:
`x + ∑_{l=k}^{i} (u_l - w_l)`. -/
def tailStock (w u : ℕ → ℝ) (k : ℕ) (x : ℝ) (i : ℕ) : ℝ :=
  x + ∑ l ∈ Finset.Ico k (i + 1), (u l - w l)

/-- The cost of periods `k, …, T - 1` of the nominal problem with demand `w`, from the stock `x`
at the beginning of period `k`: `∑_{i=k}^{T-1} (C(u_i) + R(x_{i+1}))`. -/
noncomputable def tailCost (M : Model) (w : ℕ → ℝ) (k : ℕ) (x : ℝ) (u : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.Ico k M.T, (M.C (u i) + M.R (tailStock w u k x i))

/-- `u` is optimal for the nominal problem that remains from period `k` and stock `x`: it is
nonnegative on periods `k, …, T - 1` and minimizes `tailCost` over all such sequences. -/
def IsTailOptimal (M : Model) (w : ℕ → ℝ) (k : ℕ) (x : ℝ) (u : ℕ → ℝ) : Prop :=
  (∀ i ∈ Finset.Ico k M.T, 0 ≤ u i) ∧
    ∀ u' : ℕ → ℝ, (∀ i ∈ Finset.Ico k M.T, 0 ≤ u' i) →
      tailCost M w k x u ≤ tailCost M w k x u'

/-- The order of Definition 3.1 with thresholds `s`, `S` at stock `x`:
`S - x` if `x < s` and `0` otherwise. -/
noncomputable def sSOrder (s S x : ℝ) : ℝ := if x < s then S - x else 0

/-- `sSStock s S w k x n` is the stock at the beginning of period `k + n` when the rule with
thresholds `(s_i, S_i)` is followed from period `k` and stock `x`, against the demand `w`. -/
noncomputable def sSStock (s S w : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => sSStock s S w k x n +
      sSOrder (s (k + n)) (S (k + n)) (sSStock s S w k x n) - w (k + n)

/-- The order of period `i ≥ k` under that rule. Its values at `i < k` are never used. -/
noncomputable def sSPolicy (s S w : ℕ → ℝ) (k : ℕ) (x : ℝ) (i : ℕ) : ℝ :=
  sSOrder (s i) (S i) (sSStock s S w k x (i - k))

end RobustInventory.SingleStation.Supplement


