-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_IsConeRule
-- name    : BauerleRiederMDP_TransactionCosts_IsConeRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:24.073223+00:00
-- url     : https://prove2.me/theorems/5df4b23b-d573-4803-8212-518c5c49a889
-- title:
--   The set $\Delta$ of buy/hold/sell rules, (4.26)
-- statement:
--   $\Delta$ consists of all functions $f:E\to\mathbb R_+$ (the amount held in the stock after transaction) for which there are constants $0\le q_-\le q_+\le\infty$ and measurable $f_+,f_-:E\to\mathbb R_+$ with
--   $$f(x_0,x_1)=\begin{cases}f_+(x_0,x_1), & \frac{x_1}{x_0}>q_+,\\ x_1, & q_-\le\frac{x_1}{x_0}\le q_+,\\ f_-(x_0,x_1), & \frac{x_1}{x_0}<q_-,\end{cases}\tag{4.26}$$
--   and $f_+(x_0,x_1)<x_1$, $f_-(x_0,x_1)>x_1$. Such a rule sells stock when the stock-to-bond ratio is above $q_+$, buys when it is below $q_-$, and does not trade in between; the regions are cones.
--
--   **Formalization Note** The inequalities $f_+<x_1$, $f_->x_1$ are imposed on the regions where $f=f_+$, resp. $f=f_-$ (imposed everywhere, $f_+<x_1$ would fail at $x_1=0$). The region conditions are imposed at every $x\in E\setminus\{(0,0)\}$, where $x_1/x_0$ is defined.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Proposition 4.5.2, eq. (4.26), p.109 (PDF 123)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_stateSpace
import Definitions.Def_BauerleRiederMDP_TransactionCosts_ratio

open scoped ENNReal

namespace BauerleRiederMDP.TransactionCosts

/-- The set `Δ` of Proposition 4.5.2 (Bäuerle & Rieder 2011, (4.26), p.109, PDF 123): all
functions `f : E → ℝ₊` (the amount invested in the stock after transaction) such that there
exist constants `0 ≤ q₋ ≤ q₊ ≤ ∞` and measurable functions `f₊, f₋ : E → ℝ₊` with
`f(x₀, x₁) = f₊(x₀, x₁)` if `x₁/x₀ > q₊`, `f(x₀, x₁) = x₁` if `q₋ ≤ x₁/x₀ ≤ q₊`,
`f(x₀, x₁) = f₋(x₀, x₁)` if `x₁/x₀ < q₋`, and `f₊(x₀, x₁) < x₁`, `f₋(x₀, x₁) > x₁`.

**Formalization Note.** `q₋, q₊ ∈ [0, ∞]` are in `ℝ≥0∞` and `x₁/x₀` is `ratio x`. The
inequalities `f₊ < x₁` and `f₋ > x₁` are required on the regions where `f = f₊`, resp.
`f = f₋` (required everywhere, `f₊(x) < x₁` would fail at `x₁ = 0`, since `f₊ ≥ 0`). The three
region conditions are imposed at every `x ∈ E` with `x ≠ (0, 0)`, where `x₁/x₀` is defined;
`f₊, f₋` are measurable maps on `ℝ × ℝ`, nonnegative on `E`. -/
def IsConeRule (f : ℝ × ℝ → ℝ) : Prop :=
  (∀ x ∈ stateSpace, 0 ≤ f x) ∧
  ∃ qm qp : ℝ≥0∞, qm ≤ qp ∧ ∃ fp fm : ℝ × ℝ → ℝ, Measurable fp ∧ Measurable fm ∧
    (∀ x ∈ stateSpace, 0 ≤ fp x ∧ 0 ≤ fm x) ∧
    ∀ x ∈ stateSpace, x ≠ 0 →
      (qp < ratio x → f x = fp x ∧ fp x < x.2) ∧
      (qm ≤ ratio x → ratio x ≤ qp → f x = x.2) ∧
      (ratio x < qm → f x = fm x ∧ x.2 < fm x)

end BauerleRiederMDP.TransactionCosts


