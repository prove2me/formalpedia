-- Prove2me | Definitions.Def_RareDisease_ExogOutcome_Setting
-- name    : RareDisease_ExogOutcome_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T09:42:31.219623+00:00
-- url     : https://prove2.me/theorems/d5215179-ede9-4e4a-93fe-ad8b8cd9d861
-- title:
--   §3.1–§3.2, Setting (2B) — consortium price, outcome-based payment: policies, profit (9), best responses, welfare (7), spending (10), optimal policies, αmax
-- statement:
--   This file sets up the three-stage Stackelberg game of Setting (2B): the unit selling price $p$ is fixed by a consortium and the manufacturer is paid only when the drug is efficacious for the patient ("No Cure No Pay"). The market size is scaled to one, patient valuations are uniform on $[0,1]$, $k$ is the R&D cost scale and $B$ the government's subsidy budget.
--
--   1. A **subsidy policy** is a pair $(\alpha,\beta)$ with $\alpha\in[0,1)$ (the government's share of the R&D cost $ke^2$) and $\beta\in[0,1)$ (its share of the unit price).
--   2. Given a policy and a target efficacy $e$, the **manufacturer's profit** is the bracket of (9),
--   $$\pi_m(e) = e\,p\,[1-(1-\beta)p] - (1-\alpha)k e^2 .$$
--   3. The manufacturer's **best responses** to $(\alpha,\beta)$ are the maximizers of $\pi_m$ over all efficacies $e>0$.
--   4. The **patient welfare** (7) and the **government spending** (the left side of the budget constraint in (10)) at efficacy $e$ are
--   $$W = \tfrac12\, e\,(1-(1-\beta)p)^2, \qquad M = \alpha k e^2 + e\,\beta p\,[1-(1-\beta)p].$$
--   5. A policy $(\alpha,\beta)$ is **optimal** for the government's problem (10) when it has a best response $e$ with $M\le B$, and the welfare at $e$ is at least the welfare of every policy $(\alpha',\beta')$ at every one of its best responses $e'$ whose spending is at most $B$.
--   6. $\alpha_{\max}$ is the **largest manufacturer subsidy** $\alpha\in[0,1)$ that, with $\beta=0$, has a best response whose spending is within the budget (p. 15: "the maximum manufacturer subsidy that satisfies the binding budget constraint when $\beta=0$").
--
--   Every result of the mission is stated about these objects; the reduced forms (19) and (20) are theorems about them, not definitions.
--
--   **Formalization Note** The efficacy ranges over all $e>0$ and is not bounded by $1$, as in the paper, which never imposes $e\le1$ in (9). Welfare is written in its closed form, the right-hand side of (7). The predicate `IsAlphaMax k p B a` says that $a$ is the greatest element of the set of affordable manufacturer-only subsidies; its closed form is part of the goal theorem, not of the definition.
-- source:
--   Olsder, Martagan, Tang, Improving Access to Rare Disease Treatments: Optimal Subsidies, Pricing, and Payment, SSRN working paper 3481150 (version of 2019-11-13), pp. 8–11, §3.1, §3.2.2, (7), (9), (10); p. 15, definition of αmax after (20)

import Mathlib
import Definitions.Def_RareDisease_Endogenous_Setting

namespace RareDisease.ExogOutcome

/-- The manufacturer's profit in Setting (2B), the bracket of (9): with the price `p` fixed by
the consortium, R&D cost scale `k` and target efficacy `e`,
`e p [1 - (1 - β) p] - (1 - α) k e²`. -/
def profit (k p α β e : ℝ) : ℝ :=
  e * p * (1 - (1 - β) * p) - (1 - α) * k * e ^ 2

/-- Patient welfare (7): `W = ½ e (1 - (1 - β) p)²`. -/
noncomputable def welfare (p β e : ℝ) : ℝ :=
  e * (1 - (1 - β) * p) ^ 2 / 2

/-- Government spending, the left side of the budget constraint in (10):
`α k e² + e β p [1 - (1 - β) p]`. -/
def spend (k p α β e : ℝ) : ℝ :=
  α * k * e ^ 2 + e * β * p * (1 - (1 - β) * p)

/-- The manufacturer's best responses in Setting (2B): the maximizers of the profit (9) over
target efficacies `e > 0`. -/
def BR (k p α β : ℝ) : Set ℝ :=
  {e | 0 < e ∧ ∀ e' : ℝ, 0 < e' → profit k p α β e' ≤ profit k p α β e}

/-- `(α, β)` is an optimal subsidy policy of the government's problem (10) in Setting (2B)
with budget `B`: it is a policy, it has a best response of the manufacturer at which the
spending is within the budget, and the welfare there is at least the welfare of every policy
at every one of its best responses whose spending is within the budget. -/
def IsOptimal (k p B α β : ℝ) : Prop :=
  RareDisease.Endogenous.IsPolicy α β ∧ ∃ e ∈ BR k p α β, spend k p α β e ≤ B ∧
    ∀ α' β' : ℝ, RareDisease.Endogenous.IsPolicy α' β' → ∀ e' ∈ BR k p α' β', spend k p α' β' e' ≤ B →
      welfare p β' e' ≤ welfare p β e

/-- `a` is `α_max` (p. 15): the largest manufacturer subsidy `α ∈ [0,1)` that, together with
`β = 0`, has a best response of the manufacturer at which the spending is within the budget. -/
def IsAlphaMax (k p B a : ℝ) : Prop :=
  IsGreatest {α : ℝ | α ∈ Set.Ico (0 : ℝ) 1 ∧ ∃ e ∈ BR k p α 0, spend k p α 0 e ≤ B} a

end RareDisease.ExogOutcome


