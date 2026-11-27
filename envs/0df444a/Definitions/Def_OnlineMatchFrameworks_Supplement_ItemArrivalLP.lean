-- Prove2me | Definitions.Def_OnlineMatchFrameworks_Supplement_ItemArrivalLP
-- name    : OnlineMatchFrameworks_Supplement_ItemArrivalLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:22:04.471425+00:00
-- url     : https://prove2.me/theorems/31b2bf7b-9c43-4447-b620-5ba9147beb35
-- title:
--   Linear program (6) for item arrivals
-- statement:
--   For the star problem with item arrivals and patience $\theta$, linear program (6) is
--
--   $$
--   \mathrm{LP}=\max\ \sum_iw_ix_ip_i
--   $$
--
--   subject to
--
--   1. $\sum_ix_ip_i\le1$ (6a);
--   2. $\sum_ix_i\le\theta$ (6b);
--   3. $x_i\le1-(1-q_i)^\theta$ for every $i$ (6c);
--   4. $x_i\ge0$ for every $i$ (6d).
--
--   An **optimal solution** is a feasible point of largest objective. The algorithm for item arrivals is computed from one.
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, §5.3, LP (6), p.27

import Definitions.Def_OnlineMatchFrameworks_Supplement_ItemArrival

open scoped BigOperators

namespace OnlineMatchFrameworks.Supplement

namespace ItemArrivalInstance

variable {U : Type*} [Fintype U]

/-- **The objective of LP (6).** arXiv:1907.03963v6, (6), p.27: `∑_i w_i x_i p_i`. -/
def lpObjective (G : ItemArrivalInstance U) (x : U → ℝ) : ℝ :=
  ∑ i, G.w i * x i * G.p i

/-- **The feasible set of LP (6).** arXiv:1907.03963v6, (6a)–(6d), p.27. -/
structure IsLPFeasible (G : ItemArrivalInstance U) (x : U → ℝ) : Prop where
  /-- (6a) -/
  sale_le_one : ∑ i, x i * G.p i ≤ 1
  /-- (6b) -/
  offers_le_patience : ∑ i, x i ≤ (G.patience : ℝ)
  /-- (6c) -/
  le_arrived : ∀ i, x i ≤ 1 - (1 - G.q i) ^ G.patience
  /-- (6d) -/
  nonneg : ∀ i, 0 ≤ x i

/-- **An optimal solution of LP (6).** arXiv:1907.03963v6, p.27: "Our algorithm first solves the LP (6)
to obtain an optimal solution". Its objective is the paper's `LP`. -/
def IsLPOptimal (G : ItemArrivalInstance U) (x : U → ℝ) : Prop :=
  G.IsLPFeasible x ∧ ∀ y, G.IsLPFeasible y → G.lpObjective y ≤ G.lpObjective x

end ItemArrivalInstance

end OnlineMatchFrameworks.Supplement


