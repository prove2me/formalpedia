-- Prove2me | Definitions.Def_MDPFinance_MeanVariance_TransactionCostOperators
-- name    : MDPFinance_MeanVariance_TransactionCostOperators
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:06:51.056869+00:00
-- url     : https://prove2.me/theorems/0c47765c-30bd-475f-8ee1-f09dd15c3d8a
-- title:
--   The maximal-reward operator $T_n$, the value-function class $\mathbb{M}$, and buy/hold/sell decision rules
-- statement:
--   The one-step operator $T_n v(x_0,x_1) := \sup_{a\in\mathrm{Arange}(x_0,x_1)}
--   \mathbb{E}\big[v\big(h(x_0,x_1,a)(1+i_{n+1}),\,a\,\tilde R_{n+1}\big)\big]$
--   (Bäuerle–Rieder, p. 107-108). A function $v$ lies in the class $\mathbb{M}$ if it is increasing in
--   each coordinate, concave, and homogeneous of degree $\gamma$ (`IsInIM`) — the book's $\mathbb{M}
--   := \{v\in\mathbb{B}_b^+ \mid v \text{ increasing, concave, homogeneous of degree }\gamma\}$,
--   with the boundedness clause elided since no result of this chunk needs it beyond existence. A
--   function $f$ is a **buy/hold/sell decision rule** (`IsBuyHoldSellRule`, Eq. (4.26)) if there are
--   thresholds $0\le q^-\le q^+\le\infty$ and measurable $f^+,f^-$ with
--   $$f(x_0,x_1) = \begin{cases} f^+(x_0,x_1) & x_1/x_0 > q^+ \\ x_1 & q^-\le x_1/x_0\le q^+ \\
--   f^-(x_0,x_1) & x_1/x_0 < q^-\end{cases}$$
--   and $f^+(x_0,x_1) < x_1 < f^-(x_0,x_1)$ outside the hold region: $f^+$ sells stock down to the
--   threshold, $f^-$ buys up to it.
--
--   **Formalization Note.** `IsBuyHoldSellRule` uses `EReal` for the thresholds $q^-,q^+$ so that
--   $q^+=\infty$ (never sell) is expressible exactly as the book allows.
--
--   **Formalization Note (moderation).** $\mathbb{M}$ includes the book's $v\in\mathbb{B}_b^+$
--   clause (measurable, $v^+\le c\,b$ on $E$) and its monotonicity, concavity and homogeneity are
--   required on the state space $E$ only (a function on $\mathbb{R}^2$ extended arbitrarily off
--   $E$ is not constrained there); the buy/hold/sell regions are defined through the ratio in
--   $[0,\infty]$ on $E$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 107-109, PDF 121-123, unnumbered displays and Eq. (4.26)

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The maximal reward operator `T_n v(x) := sup_{a ∈ Arange(x)} 𝔼[v(h(x,a)(1+i_{n+1}),
a\,\tilde R_{n+1})]` (Bäuerle–Rieder, p. 107-108, PDF 122). -/
noncomputable def TransactionCostMarket.T (M : TransactionCostMarket Ω) (n : ℕ)
    (v : ℝ × ℝ → ℝ) (x0 x1 : ℝ) : ℝ :=
  ⨆ a ∈ M.Arange x0 x1, ∫ ω, v (M.h x0 x1 a * (1 + M.i (n + 1)), a * M.Rtilde (n + 1) ω) ∂M.measIP

/-- `v ∈ IM` (Bäuerle–Rieder, p. 107, PDF 121): `v ∈ IB_b^+` for the upper bounding function
`b(x) = 1 + x0 + x1` (measurable, `v^+ ≤ c·b` on `E`), increasing in each component, concave
and homogeneous of degree `γ` on the state space `E = ℝ_{\ge0}²`. -/
def IsInIM (γ : ℝ) (v : ℝ × ℝ → ℝ) : Prop :=
  Measurable v ∧ (∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ Estate, max (v x) 0 ≤ c * (1 + x.1 + x.2)) ∧
  (∀ x ∈ Estate, ∀ y ∈ Estate, x.1 ≤ y.1 → x.2 ≤ y.2 → v x ≤ v y) ∧
    ConcaveOn ℝ Estate v ∧ IsHomogeneousDeg γ v

/-- `f ∈ Δ` (Bäuerle–Rieder, Eq. (4.26), p. 109, PDF 123): `f` is a buy/hold/sell decision rule,
i.e. there are `0 ≤ q^- ≤ q^+ ≤ ∞` and measurable `f^+, f^- : E → ℝ_{\ge0}` with
`f(x0,x1) = f^+(x0,x1)` if `x1/x0 > q^+`, `= x1` if `q^- ≤ x1/x0 ≤ q^+`, `= f^-(x0,x1)` if
`x1/x0 < q^-`, and `f^+(x0,x1) < x1`, `f^-(x0,x1) > x1` (on the respective regions of `E`; the
ratio `x1/x0` is `ratio x0 x1 ∈ [0,∞]`). -/
def IsBuyHoldSellRule (f : ℝ × ℝ → ℝ) : Prop :=
  ∃ qm qp : EReal, 0 ≤ qm ∧ qm ≤ qp ∧ ∃ fp fm : ℝ × ℝ → ℝ, Measurable fp ∧ Measurable fm ∧
    (∀ x ∈ Estate, qp < ratio x.1 x.2 → f x = fp x ∧ fp x < x.2) ∧
    (∀ x ∈ Estate, qm ≤ ratio x.1 x.2 → ratio x.1 x.2 ≤ qp → f x = x.2) ∧
    (∀ x ∈ Estate, ratio x.1 x.2 < qm → f x = fm x ∧ x.2 < fm x)

end MDPFinance.MeanVariance


