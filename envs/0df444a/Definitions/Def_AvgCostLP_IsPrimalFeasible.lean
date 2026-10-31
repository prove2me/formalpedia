-- Prove2me | Definitions.Def_AvgCostLP_IsPrimalFeasible
-- name    : AvgCostLP_IsPrimalFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:28:26.734583+00:00
-- url     : https://prove2.me/theorems/50d5a964-2815-42f1-ae52-3e0ca3950da4
-- title:
--   (3.5), (3.10) — the primal program (P) on occupation measures
-- statement:
--   The **primal program** (P) minimizes $\langle\gamma,c\rangle=\int c\,d\gamma$ over $\gamma\in\mathbb M^+_w(\Gamma)$ subject to
--   $$\gamma(\Gamma)=1,\qquad\hat\gamma(B)=\int_\Gamma q(B\mid x,a)\,\gamma(d(x,a))\quad\forall B\in\mathcal B(\mathbb X), \tag{3.5}$$
--   where $\mathbb M^+_w(\Gamma)$ is the set of nonnegative Borel measures on $\Gamma$ that integrate the weight $w=1+c$, and $\hat\gamma$ is the marginal of $\gamma$ on $\mathbb X$. `primalValues` is the set of objective values $\int c\,d\gamma$ of feasible $\gamma$: its infimum is $\inf(\mathrm P)$, (P) is **consistent** when it is nonempty and **solvable** when the infimum is attained. `residual` is the expression $\int h\,d\hat\gamma-\int_\Gamma\int_{\mathbb X}h(y)\,q(dy\mid x,a)\,\gamma(d(x,a))$ of (5.3).
--
--   **Formalization Note** Measures on $\Gamma$ are measures on $\mathbb X\times\mathbb A$ with $\gamma(\Gamma^c)=0$. Since feasibility includes $\int(1+c)\,d\gamma<\infty$, the objective value is the real number $\int c\,d\gamma$.
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, §3.1, (3.5) p.10, (3.10) p.11

import Mathlib
import Definitions.Def_AvgCostLP_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AvgCostLP

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

/-- Yu, arXiv:1905.12095v3, §3.1, (3.5) and (3.10), p.10–11: `γ` is a feasible solution of the
primal program (P), i.e. `γ ∈ M⁺_w(Γ)` is a nonnegative Borel measure on `Γ` with
`∫ w dγ < ∞` for the weight `w = 1 + c`, `γ(Γ) = 1`, and its marginal `γ̂` on `X` satisfies
`γ̂(B) = ∫_Γ q(B | x, a) γ(d(x, a))` for every Borel set `B ⊂ X`.

**Formalization Note** A measure on `Γ` is encoded as a measure on `X × A` concentrated on `Γ`
(`γ(Γᶜ) = 0`), as the paper itself identifies them (p.9). The integrals are `lintegral`s of
`[0, +∞]`-valued functions, and `γ̂ = γ ∘ Prod.fst⁻¹`. -/
def IsPrimalFeasible (M : Model X A) (γ : Measure (X × A)) : Prop :=
  γ M.graphᶜ = 0 ∧ γ M.graph = 1 ∧ ∫⁻ p, (1 + M.c p) ∂γ < ⊤ ∧
    ∀ B : Set X, MeasurableSet B → γ.map Prod.fst B = ∫⁻ p, M.q p B ∂γ

/-- Yu, arXiv:1905.12095v3, (3.10), p.11: the set of objective values `⟨γ, c⟩ = ∫ c dγ` of the
feasible solutions of (P). Its infimum is `inf(P)`; (P) is *consistent* when it is nonempty and
*solvable* when the infimum is attained.

**Formalization Note** Feasibility gives `∫ c dγ < ∞`, so the real number `(∫ c dγ).toReal` is the
objective value exactly. -/
def primalValues (M : Model X A) : Set ℝ :=
  {r | ∃ γ : Measure (X × A), IsPrimalFeasible M γ ∧ r = (∫⁻ p, M.c p ∂γ).toReal}

/-- Yu, arXiv:1905.12095v3, (3.3)/(3.7) and (5.3), pp.11, 20: for a measure `γ` on `X × A` and a
function `h` on `X`, the residual `∫_X h(x) γ̂(dx) − ∫_Γ ∫_X h(y) q(dy | x, a) γ(d(x, a))`, i.e.
the pairing `⟨L₁γ, h⟩` of the second component of `Lγ` with `h`. -/
noncomputable def residual (M : Model X A) (γ : Measure (X × A)) (h : X → ℝ) : ℝ :=
  ∫ x, h x ∂(γ.map Prod.fst) - ∫ p, ∫ y, h y ∂(M.q p) ∂γ

end AvgCostLP


