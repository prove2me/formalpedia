-- Prove2me | Definitions.Def_RareDisease_Endogenous_Setting
-- name    : RareDisease_Endogenous_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:31.763114+00:00
-- url     : https://prove2.me/theorems/29be6845-414f-4250-8d48-88f9ce7b67fa
-- title:
--   §3.1–§3.2 — manufacturer pricing with sales- or outcome-based payment
-- statement:
--   The paper studies a government, a drug manufacturer, and patients in a market of size one. The government chooses an R&D cost share $\alpha\in[0,1)$ and a patient price share $\beta\in[0,1)$. Given these shares, the manufacturer chooses a nonnegative price $p$ and a positive target efficacy $e$.
--
--   In the **sales-based scheme** (1A), manufacturer profit, patient welfare, and government spending are respectively
--   $$
--   \pi_A=p\left(1-\frac{(1-\beta)p}{e}\right)-(1-\alpha)ke^2,\qquad
--   W_A=\frac{(e-(1-\beta)p)^2}{2e},\qquad
--   M_A=\alpha ke^2+\beta p\left(1-\frac{(1-\beta)p}{e}\right).
--   $$
--   In the **outcome-based scheme** (1B), they are
--   $$
--   \pi_B=ep(1-(1-\beta)p)-(1-\alpha)ke^2,\qquad
--   W_B=\frac e2(1-(1-\beta)p)^2,\qquad
--   M_B=\alpha ke^2+e\beta p(1-(1-\beta)p).
--   $$
--   For each scheme, the best-response set contains every $(p,e)$ maximizing the manufacturer's profit over $p\ge0$, $e>0$. A government policy is optimal when it is feasible at a best response and its welfare is at least that of every other feasible policy at every best response. The displayed subsidy $\alpha^*=(1+128Bk-\sqrt{256Bk+1})/(128Bk)$ names the candidate policy of Proposition 1; it does not define optimality.
--
--   These definitions keep the manufacturer and government optimization problems separate, so the later reduced formulas are results about the game.
--
--   **Formalization Note** The paper's maximizations place no upper bound on $e$, despite describing it as a probability. The price is restricted to $p\ge0$. Lean's formulas for demand and welfare use the paper's unclipped expressions; at the derived best responses, their demand is nonnegative. Division by $e$ is evaluated only at best responses with $e>0$.
-- source:
--   Olsder, Martagan, Tang, Improving Access to Rare Disease Treatments: Optimal Subsidies, Pricing, and Payment, SSRN working paper 3481150 (version of 2019-11-13), pp. 8–11, §3.1–§3.2, equations (1)–(3), (5)–(8), (10)

import Mathlib

namespace RareDisease.Endogenous

/-- The subsidy shares in §3.1 are both in `[0,1)`. -/
def IsPolicy (α β : ℝ) : Prop := α ∈ Set.Ico (0 : ℝ) 1 ∧ β ∈ Set.Ico (0 : ℝ) 1

/-- Manufacturer profit in Setting (1A), equation (3). -/
noncomputable def profitA (k α β p e : ℝ) : ℝ :=
  p * (1 - (1 - β) * p / e) - (1 - α) * k * e ^ 2

/-- Patient welfare in Setting (1A), equation (2). -/
noncomputable def welfareA (β p e : ℝ) : ℝ :=
  (e - (1 - β) * p) ^ 2 / (2 * e)

/-- Government spending in Setting (1A), equation (5). -/
noncomputable def spendA (k α β p e : ℝ) : ℝ :=
  α * k * e ^ 2 + β * p * (1 - (1 - β) * p / e)

/-- Manufacturer profit in Setting (1B), equation (8). -/
def profitB (k α β p e : ℝ) : ℝ :=
  e * p * (1 - (1 - β) * p) - (1 - α) * k * e ^ 2

/-- Patient welfare in Setting (1B), equation (7). -/
noncomputable def welfareB (β p e : ℝ) : ℝ :=
  e * (1 - (1 - β) * p) ^ 2 / 2

/-- Government spending in Setting (1B), equation (10). -/
def spendB (k α β p e : ℝ) : ℝ :=
  α * k * e ^ 2 + e * β * p * (1 - (1 - β) * p)

/-- All manufacturer best responses for sales-based payment. -/
def BRA (k α β : ℝ) : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ 0 < x.2 ∧
    ∀ p e : ℝ, 0 ≤ p → 0 < e → profitA k α β p e ≤ profitA k α β x.1 x.2}

/-- All manufacturer best responses for outcome-based payment. -/
def BRB (k α β : ℝ) : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ 0 < x.2 ∧
    ∀ p e : ℝ, 0 ≤ p → 0 < e → profitB k α β p e ≤ profitB k α β x.1 x.2}

/-- Government optimality for Setting (1A): an attained feasible welfare maximum over
all feasible policies and all manufacturer best responses. -/
def IsOptimalA (k B α β : ℝ) : Prop :=
  IsPolicy α β ∧ ∃ x ∈ BRA k α β, spendA k α β x.1 x.2 ≤ B ∧
    ∀ α' β' : ℝ, ∀ y ∈ BRA k α' β', IsPolicy α' β' →
      spendA k α' β' y.1 y.2 ≤ B → welfareA β' y.1 y.2 ≤ welfareA β x.1 x.2

/-- Government optimality for Setting (1B), with outcome-contingent spending. -/
def IsOptimalB (k B α β : ℝ) : Prop :=
  IsPolicy α β ∧ ∃ x ∈ BRB k α β, spendB k α β x.1 x.2 ≤ B ∧
    ∀ α' β' : ℝ, ∀ y ∈ BRB k α' β', IsPolicy α' β' →
      spendB k α' β' y.1 y.2 ≤ B → welfareB β' y.1 y.2 ≤ welfareB β x.1 x.2

/-- The manufacturer-only subsidy of Proposition 1. -/
noncomputable def alphaStar (k B : ℝ) : ℝ :=
  (1 + 128 * B * k - Real.sqrt (256 * B * k + 1)) / (128 * B * k)

end RareDisease.Endogenous


