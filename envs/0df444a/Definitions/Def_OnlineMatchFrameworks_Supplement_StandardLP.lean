-- Prove2me | Definitions.Def_OnlineMatchFrameworks_Supplement_StandardLP
-- name    : OnlineMatchFrameworks_Supplement_StandardLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:23:02.760014+00:00
-- url     : https://prove2.me/theorems/bd1485a1-6b32-5186-a93f-790644873642
-- title:
--   The standard LP: (1) with (1a)–(1c) only
-- statement:
--   The standard linear programming relaxation of vertex-weighted online matching with patience is LP (1) without the family (1d):
--
--   $$
--   \mathrm{LP}(G)=\max\ \sum_{u\in U}\sum_{v\in V}x_{u,v}p_{u,v}w_u
--   $$
--
--   subject to $\sum_vx_{u,v}p_{u,v}\le1$ for each $u$, $\sum_ux_{u,v}p_{u,v}\le1$ for each $v$, $\sum_ux_{u,v}\le\mathbb E[\theta_v]$ for each $v$, and $0\le x_{u,v}\le1$. Its ratio to the offline optimum is the stochasticity gap studied in §6.1.
--
--   **Formalization Note** The budget $\mathbb E[\theta_v]$ is an argument in $[0,\infty]$. The published feasible set of LP (1) contains (1d), so it is not reused; the objective is.
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, §6.1, p.30

import Definitions.Def_OnlineMatchFrameworks_LP

open scoped BigOperators ENNReal

namespace OnlineMatchFrameworks.Supplement

variable {U V : Type*} [Fintype U] [Fintype V]

/-- **The feasible set of the standard LP.** arXiv:1907.03963v6, §6.1, p.30: LP (1) with the constraints
(1a)–(1c) and `0 ≤ x ≤ 1`, "excluding our additional family of constraints (1d)". `E v` is the right
side `E[θ_v]` of (1c).

**Formalization Note.** The published `OnlineMatchFrameworks.Instance.IsFeasible` includes (1d), so it
cannot be reused. -/
structure IsStandardFeasible (G : OnlineMatchFrameworks.Instance U V) (E : V → ℝ≥0∞)
    (x : U → V → ℝ) : Prop where
  /-- (1a) -/
  item_le_one : ∀ u, ∑ v, x u v * G.p u v ≤ 1
  /-- (1b) -/
  customer_le_one : ∀ v, ∑ u, x u v * G.p u v ≤ 1
  /-- (1c) -/
  probes_le_budget : ∀ v, ENNReal.ofReal (∑ u, x u v) ≤ E v
  /-- `0 ≤ x_{u,v}` -/
  nonneg : ∀ u v, 0 ≤ x u v
  /-- `x_{u,v} ≤ 1` -/
  le_one : ∀ u v, x u v ≤ 1

/-- **The value of the standard LP.** arXiv:1907.03963v6, §6.1, p.30, with the objective
`∑_u ∑_v x_{u,v} p_{u,v} w_u` of LP (1).

**Formalization Note.** The feasible set contains `0` and lies in the unit box, so the real supremum is
the LP optimum. -/
noncomputable def standardLPValue (G : OnlineMatchFrameworks.Instance U V) (E : V → ℝ≥0∞) : ℝ :=
  sSup (G.objective '' {x | IsStandardFeasible G E x})

end OnlineMatchFrameworks.Supplement


