-- Prove2me | Definitions.Def_RobustRiskOpt_Admissible
-- name    : RobustRiskOpt_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:41:08.738124+00:00
-- url     : https://prove2.me/theorems/ee8855c3-0a32-4304-8564-54f7536fb8e2
-- title:
--   The space $\mathbb R^n$, the budget, the admissible set $\mathcal G$ of (7), the value $\rho(X;\mathcal G)$ and the optimizers $\mathcal G_X(\rho)$
-- statement:
--   Fix a probability space $(\Omega,\mathcal F,\mathbb P)$ and write $\mathbb R^n$ for the $n$-dimensional Euclidean space. For a random vector $X$ with law $\mu_X$, a measurable price density $\gamma:\mathbb R^n\to(0,\infty)$ and a measurable $g:\mathbb R^n\to\mathbb R$, the **budget** of $g$ is the expectation
--
--   $$
--   \mathbb E[g(X)\gamma(X)]=\mathbb E_{\mu_X}[(\gamma g)_+]-\mathbb E_{\mu_X}[(\gamma g)_-].
--   $$
--
--   For measurable bounds $v:\mathbb R^n\to\mathbb R\cup\{-\infty\}$, $w:\mathbb R^n\to\mathbb R$ and a constant $x_0\in\mathbb R$, the **admissible set** is
--
--   $$
--   \mathcal G=\{g\ \text{measurable}: v\le g\le w\ \text{ and }\ \mathbb E[g(X)\gamma(X)]\ge x_0\}.
--   $$
--
--   For an objective functional $\rho$, the **optimal value** is $\rho(X;\mathcal G)=\inf\{\rho(g(X)):g\in\mathcal G\}$, and the **set of optimizing functions** is
--
--   $$
--   \mathcal G_X(\rho)=\{g\in\mathcal G:\rho(g(X))=\rho(X;\mathcal G)\},
--   $$
--
--   which may be empty. These objects describe the functional optimization problem (8), to minimize $\rho(g(X))$ subject to $v\le g\le w$ and $\mathbb E[\gamma(X)g(X)]\ge x_0$. It is a budget-constrained portfolio or insurance design problem.
--
--   **Formalization Note** The space $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. The budget is computed in `EReal` from two `lintegral`s: it is $+\infty$ when only the positive part has infinite integral, and such a $g$ is feasible; when both parts have infinite integral it is `⊥`, so an undefined expectation is infeasible. The bounds $v\le g\le w$ are pointwise on all of $\mathbb R^n$, as printed in (7). The lower bound is `EReal`-valued, and $v<+\infty$ follows from $\mathcal G\ne\emptyset$. The value and the optimizers are defined for an `EReal`-valued objective.
-- source:
--   Embrechts–Schied–Wang, Robustness in the Optimization of Risk Measures, arXiv:1809.09268v3, 11 Feb 2021, §2.2–§2.3, (2), p.7; (7)–(8), p.11

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace RobustRiskOpt

/-- `ℝⁿ` with the Euclidean norm `|x|` of §2.1, p.5 (Embrechts–Schied–Wang, arXiv:1809.09268v3).

**Formalization Note** `EuclideanSpace ℝ (Fin n)` and not `Fin n → ℝ`, whose norm is the sup
norm: the metrics of Example 3, p.9, and footnote 7 are Euclidean. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- The budget functional `𝔼_μ[γ g] = 𝔼[g(X) γ(X)]` of (7), p.11, for `μ = μ_X`
(Embrechts–Schied–Wang, arXiv:1809.09268v3).

**Formalization Note** This is the extended-value expectation `𝔼[(γg)₊] − 𝔼[(γg)₋]`, computed in
`EReal`. It is `+∞` when only the positive part has infinite integral, so such a `g` is feasible;
when both parts have infinite integral it is `⊤ - ⊤ = ⊥`, so an undefined expectation is
infeasible. No integrability of `γ g` is assumed. This is the reading under which the function
`ĝ = g_X 1_{Aᶜ} + w 1_A` of the proof of Theorem 1, p.29, stays in `𝒢`. -/
noncomputable def budget (μ : Measure (E n)) (γ g : E n → ℝ) : EReal :=
  ((∫⁻ x, ENNReal.ofReal (γ x * g x) ∂μ : ℝ≥0∞) : EReal) -
    ((∫⁻ x, ENNReal.ofReal (-(γ x * g x)) ∂μ : ℝ≥0∞) : EReal)

/-- The admissible set `𝒢` of (7), p.11 (Embrechts–Schied–Wang, arXiv:1809.09268v3):
`𝒢 = {g ∈ 𝒢ₙ : v ≤ g ≤ w and 𝔼[g(X)γ(X)] ≥ x₀}`, with `𝒢ₙ` the measurable functions `ℝⁿ → ℝ`
(p.5).

**Formalization Note** Measurability of `g` is Borel. The bounds `v ≤ g ≤ w` are pointwise on all
of `ℝⁿ`, as printed in (7). The lower bound `v` has values in `EReal`; the paper's `v` has values
in `ℝ ∪ {−∞}`, and `v x ≠ ⊤` follows from `𝒢 ≠ ∅` (Assumption G). -/
def admissible (P : Measure Ω) (X : Ω → E n) (v : E n → EReal) (w γ : E n → ℝ) (x₀ : ℝ) :
    Set (E n → ℝ) :=
  {g | Measurable g ∧ (∀ x, v x ≤ (g x : EReal)) ∧ (∀ x, g x ≤ w x) ∧
    (x₀ : EReal) ≤ budget (P.map X) γ g}

/-- The optimal value `ρ(X; 𝒢) = inf {ρ(g(X)) : g ∈ 𝒢}`, §2.3, p.7
(Embrechts–Schied–Wang, arXiv:1809.09268v3).

**Formalization Note** The objective is `EReal`-valued (the paper's `ρ` has values in
`ℝ ∪ {+∞}`) and the infimum is taken in `EReal`, so it is never a junk real `sInf`. -/
noncomputable def rhoInf (ρ : (Ω → ℝ) → EReal) (X : Ω → E n) (𝒢 : Set (E n → ℝ)) : EReal :=
  ⨅ g ∈ 𝒢, ρ (g ∘ X)

/-- The set of optimizing functions `𝒢_X(ρ) = {g ∈ 𝒢 : ρ(g(X)) = ρ(X; 𝒢)}`, (2), p.7
(Embrechts–Schied–Wang, arXiv:1809.09268v3). It may be empty. -/
def optimizers (ρ : (Ω → ℝ) → EReal) (X : Ω → E n) (𝒢 : Set (E n → ℝ)) : Set (E n → ℝ) :=
  {g | g ∈ 𝒢 ∧ ρ (g ∘ X) = rhoInf ρ X 𝒢}

end RobustRiskOpt


