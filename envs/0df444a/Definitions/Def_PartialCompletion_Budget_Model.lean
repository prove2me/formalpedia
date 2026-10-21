-- Prove2me | Definitions.Def_PartialCompletion_Budget_Model
-- name    : PartialCompletion_Budget_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:07.401754+00:00
-- url     : https://prove2.me/theorems/35545e54-ea93-4a9b-a15b-a5d04b411ab2
-- title:
--   §3–§4.2, pp. 7–13 — variety, completion, beneficiary effort and budget model
-- statement:
--   The nonlinear nonprofit allocation model has a continuous variety level $n\ge1$ and completion level $\alpha\in[0,1]$. Heterogeneity is $0<\theta\le2$. With quadratic self-completion cost $\beta e^2$, $\beta>0$, a beneficiary chooses effort $e^*(\alpha)=\min\{1/(2\beta),1-\alpha\}$. The nonprofit pays $\alpha g(n)$ and maximizes
--
--   $$
--   W(n,\alpha)=\alpha\left(1-\frac{\theta}{4n}\right)-\alpha g(n)+e^*(\alpha)-\beta e^*(\alpha)^2
--   $$
--
--   subject to $\alpha g(n)\le B$ for budget $B\ge0$. Its cost function satisfies $g(1)>0$, $g'(n)>0$, and $g''(n)\ge0$ for $n\ge1$. Some $n\ge1$ has $g(n)<1-\theta/(4n)$. The model also defines the unconstrained optimum's variety characterization, its completion formula, and the appendix functions $\Lambda_1$ and $\Lambda_2$. These shared objects keep all milestone statements on the same economic model.
--
--   **Formalization Note** The derivative functions are explicit and satisfy `HasDerivAt` on $[1,\infty)$. The strict positivity of $\theta$ and $\beta$ is explicit; the paper gives $\theta\le2$ and assumes an increasing effort cost. Optimality includes both feasibility and maximality. Division by $n$ and $g(n)$ is used in claims restricted to $n\ge1$.
-- source:
--   Zhang, Atasu & Ramachandran, Partial Completion as a Nonprofit Strategy, SSRN 3684891, pp. 7–13, §3–§4.2; Online Appendix pp. 2–3 (PDF 35–36)

import Mathlib

namespace PartialCompletion.Budget

/-- The quadratic self-completion model of §3–§4.2. -/
structure Model where
  θ : ℝ
  β : ℝ
  g : ℝ → ℝ
  g' : ℝ → ℝ
  g'' : ℝ → ℝ

/-- Standing assumptions on the physical domain n ≥ 1. -/
structure Model.Standing (M : Model) : Prop where
  θ_pos : 0 < M.θ
  θ_le_two : M.θ ≤ 2
  β_pos : 0 < M.β
  hasDerivAt_g : ∀ n : ℝ, 1 ≤ n → HasDerivAt M.g (M.g' n) n
  hasDerivAt_g' : ∀ n : ℝ, 1 ≤ n → HasDerivAt M.g' (M.g'' n) n
  g_one_pos : 0 < M.g 1
  g'_pos : ∀ n : ℝ, 1 ≤ n → 0 < M.g' n
  g''_nonneg : ∀ n : ℝ, 1 ≤ n → 0 ≤ M.g'' n
  worthwhile : ∃ n : ℝ, 1 ≤ n ∧ M.g n < 1 - M.θ / (4 * n)

/-- Optimal beneficiary effort at completion level α. -/
noncomputable def effort (M : Model) (α : ℝ) : ℝ :=
  min (1 / (2 * M.β)) (1 - α)

/-- Total net benefit at a decision pair (n, α). -/
noncomputable def W (M : Model) (p : ℝ × ℝ) : ℝ :=
  p.2 * (1 - M.θ / (4 * p.1)) - p.2 * M.g p.1 +
    effort M p.2 - M.β * effort M p.2 ^ 2

/-- Variety at least one and completion between zero and one. -/
def Unconstrained : Set (ℝ × ℝ) :=
  {p | 1 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}

/-- The budget-constrained decision set. -/
def Feasible (M : Model) (B : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ Unconstrained ∧ p.2 * M.g p.1 ≤ B}

/-- Feasibility and maximal benefit among feasible decisions. -/
def IsOptimal (M : Model) (B : ℝ) (p : ℝ × ℝ) : Prop :=
  p ∈ Feasible M B ∧ IsMaxOn (W M) (Feasible M B) p

/-- Characterization of n*_NB = max{ñ, 1}. -/
def IsNNB (M : Model) (n : ℝ) : Prop :=
  1 ≤ n ∧ (n = 1 → M.θ / 4 ≤ M.g' 1) ∧
    (1 < n → M.θ / (4 * n ^ 2) = M.g' n)

/-- Unconstrained optimal completion at fixed optimal variety. -/
noncomputable def alphaAmple (M : Model) (n : ℝ) : ℝ :=
  max (1 - (M.θ / (4 * n) + M.g n) / (2 * M.β)) 0

/-- The first derivative-sign numerator on the binding-budget curve. -/
noncomputable def Λ1 (M : Model) (n : ℝ) : ℝ :=
  -n * (4 * n - M.θ) * M.g' n + M.θ * M.g n

/-- The second derivative-sign factor on the binding-budget curve. -/
noncomputable def Λ2 (M : Model) (B n : ℝ) : ℝ :=
  M.θ * (M.g n + n * M.g' n) / (4 * n ^ 2 * M.g' n) -
    2 * M.β * (1 - B / M.g n)

/-- The small-budget variety n₀, characterized by Λ₁. -/
def IsN0 (M : Model) (n : ℝ) : Prop :=
  1 ≤ n ∧ (n = 1 → Λ1 M 1 ≤ 0) ∧ (1 < n → Λ1 M n = 0)

end PartialCompletion.Budget


