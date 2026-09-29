-- Prove2me | Definitions.Def_CachonPushPull_Pareto_Contracts
-- name    : CachonPushPull_Pareto_Contracts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:23:30.173193+00:00
-- url     : https://prove2.me/theorems/bd64109e-9392-4ef0-93cc-535da276eff5
-- title:
--   Push and pull contracts, Pareto dominance, and the Pareto set of single wholesale price contracts
-- statement:
--   A *single wholesale price contract* is a pair $k = (\text{mode}, q)$ with mode push or pull and a quantity $q \in \mathbb R$. Its wholesale price is $\hat w_1(q)$ for push and $w_1(q)$ for pull, and its payoffs (retailer, supplier) are
--   $$
--   \big(\hat\pi_r(q), \hat\pi_s(q)\big) \text{ for push}, \qquad \big(\pi_r(q), \pi_s(q)\big) \text{ for pull}.
--   $$
--
--   A contract is *admissible* if $q \ge 0$ and its wholesale price $w$ satisfies $c \le w \le p$.
--
--   A contract $k'$ *Pareto dominates* $k$ if no firm is worse off under $k'$ than under $k$ and at least one firm is strictly better off (p. 224). The *Pareto set* is the set of admissible contracts that are not Pareto dominated by any admissible contract.
--
--   This is the object of Theorem 6.
--
--   **Formalization Note** The admissibility window $c \le w \le p$ is an explicit reading that the formalization adds. The paper requires $\hat w_1 < p$ for push and $w_1 = w_2 < p$ for pull, and says that contracts with $q > q^o$ "are clearly always Pareto inferior". On the unrestricted space $q \ge 0$ that remark is false: a pull contract with $q > q^o$ gives the supplier more than $\Pi^o$ and the retailer a loss, and no push or pull contract dominates it. The window is the closure of the paper's price constraints together with "the supplier does not sell below cost". For $q \ge 0$ it is equivalent to $q \le q^o$ in both modes, and to both firms earning nonnegative profit. With the window, the paper's remark holds and Theorem 6 is true as stated.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 224 (Pareto contracts), p. 226 (push and pull contracts), p. 228 (Section 4.4)

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- The two single-wholesale-price contract types of §4.4. -/
inductive Mode
  | push
  | pull
  deriving DecidableEq

/-- A single-wholesale-price contract: a mode and a quantity `q` (the retailer's prebook with
push, the supplier's production with pull). The wholesale price is the one that induces `q`:
`ŵ₁(q)` for push, `w₁(q)` for pull. -/
structure Contract where
  mode : Mode
  q : ℝ

/-- The contract's wholesale price: `ŵ₁(q)` for push, `w₁(q)` for pull. -/
noncomputable def Contract.wholesalePrice (μ : Measure ℝ) (p c v : ℝ) (k : Contract) : ℝ :=
  match k.mode with
  | .push => pushPrice μ p v k.q
  | .pull => pullPrice μ c v k.q

/-- The retailer's expected profit under a contract: `π̂_r(q)` for push, `π_r(q)` for pull. -/
noncomputable def Contract.retailerPayoff (μ : Measure ℝ) (p c v : ℝ) (k : Contract) : ℝ :=
  match k.mode with
  | .push => pushRetailerProfit μ p v k.q
  | .pull => pullRetailerProfit μ p c v k.q

/-- The supplier's expected profit under a contract: `π̂_s(q)` for push, `π_s(q)` for pull. -/
noncomputable def Contract.supplierPayoff (μ : Measure ℝ) (p c v : ℝ) (k : Contract) : ℝ :=
  match k.mode with
  | .push => pushSupplierProfit μ p c v k.q
  | .pull => pullSupplierProfit μ c v k.q

/-- An admissible contract: quantity `q ≥ 0` and wholesale price between the production cost and
the retail price, `c ≤ w ≤ p`. -/
def Contract.IsAdmissible (μ : Measure ℝ) (p c v : ℝ) (k : Contract) : Prop :=
  0 ≤ k.q ∧ c ≤ k.wholesalePrice μ p c v ∧ k.wholesalePrice μ p c v ≤ p

/-- `k'` Pareto dominates `k`: no firm is worse off under `k'` and one firm is strictly better
off (p. 224). -/
def Contract.ParetoDominates (μ : Measure ℝ) (p c v : ℝ) (k' k : Contract) : Prop :=
  k.retailerPayoff μ p c v ≤ k'.retailerPayoff μ p c v ∧
  k.supplierPayoff μ p c v ≤ k'.supplierPayoff μ p c v ∧
  (k.retailerPayoff μ p c v < k'.retailerPayoff μ p c v ∨
    k.supplierPayoff μ p c v < k'.supplierPayoff μ p c v)

/-- The Pareto set among the admissible push and pull contracts: admissible contracts that no
admissible contract Pareto dominates. -/
def paretoSet (μ : Measure ℝ) (p c v : ℝ) : Set Contract :=
  {k | k.IsAdmissible μ p c v ∧ ¬ ∃ k' : Contract, k'.IsAdmissible μ p c v ∧ k'.ParetoDominates μ p c v k}

end CachonPushPull.Pareto


