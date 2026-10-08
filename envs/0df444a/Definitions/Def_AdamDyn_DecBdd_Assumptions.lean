-- Prove2me | Definitions.Def_AdamDyn_DecBdd_Assumptions
-- name    : AdamDyn_DecBdd_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:27.394984+00:00
-- url     : https://prove2.me/theorems/aa88f8b6-964b-4002-95c6-7ef8f08a5e27
-- title:
--   Assumptions 2.2, 4.1, 4.2 i), 5.1 and 5.3 and the objective F(x) = E f(x, ξ)
-- statement:
--   Let $(\Xi,\mathfrak S)$ be a measurable space with a probability measure $\mu$ (the law of the sample $\xi$), $f:\mathbb R^d\times\Xi\to\mathbb R$, and $g_f(x,\xi)=\nabla f(x,\xi)$ its gradient in $x$. The **objective** is (2.2)
--   $$F(x)=\mathbb E f(x,\xi)=\int_\Xi f(x,\xi)\,\mu(d\xi).$$
--
--   **Assumption 2.2.** (i) for every $x$, $f(x,\cdot)$ is measurable; (ii) for $\mu$-almost every $\xi$, $f(\cdot,\xi)$ is continuously differentiable with gradient $\nabla f(\cdot,\xi)$; (iii) there is $x_*$ with $\mathbb E|f(x_*,\xi)|<\infty$ and $\mathbb E\|\nabla f(x_*,\xi)\|^2<\infty$; (iv) for every compact $K\subset\mathbb R^d$ there is $L_K>0$ with $\mathbb E\|\nabla f(x,\xi)-\nabla f(y,\xi)\|^2\le L_K^2\|x-y\|^2$ for $x,y\in K$.
--
--   **Assumption 4.1.** On a probability space $(\Omega,\mathcal F,\mathbb P)$, the sequence $(\xi_n:n\ge1)$ is iid with law $\mu$.
--
--   **Assumption 4.2 i)** with exponent $p>0$: for every compact $K$, $\sup_{x\in K}\mathbb E\|\nabla f(x,\xi)\|^p<\infty$.
--
--   **Assumption 5.1 (stepsizes).** (i) $\gamma_n>0$ for all $n$ and $\gamma_{n+1}/\gamma_n\to1$; (ii) $\sum_n\gamma_n=+\infty$ and $\sum_n\gamma_n^2<+\infty$; (iii) $0\le\alpha_n\le1$ and $0\le\beta_n\le1$ for all $n$; (iv) there are $a,b$ with $0<b<4a$, $\gamma_n^{-1}(1-\alpha_n)\to a$ and $\gamma_n^{-1}(1-\beta_n)\to b$.
--
--   **Assumption 5.3.** (i) $\nabla F$ is Lipschitz continuous; (ii) there is $C>0$ with $\mathbb E\|\nabla f(x,\xi)\|^2\le C(1+F(x))$ for all $x$; (iii)
--   $$\limsup_{n\to\infty}\Big(\frac1{\gamma_n}-\frac{1-\alpha_{n+2}}{1-\alpha_{n+1}}\,\frac1{\gamma_{n+1}}\Big)<2\Big(a-\frac b4\Big).$$
--
--   These are the hypotheses of Theorem 5.4; Assumption 2.3 (coercivity of $F$) is written directly in the theorem.
--
--   **Formalization Note** Moments of possibly non-integrable functions are lower Lebesgue integrals (`∫⁻`, values in $[0,\infty]$), so no hypothesis becomes vacuous through Lean's convention that the Bochner integral of a non-integrable function is $0$; in 5.3 ii) the moment is a Bochner integral together with its integrability, which also forces $C(1+F(x))\ge0$ as on the page. 2.2 also records that $\xi\mapsto\nabla f(x,\xi)$ is a.e. strongly measurable, which follows from (i)–(ii). 4.1 is stated for the shifted sequence $n\mapsto\xi_{n+1}$ (independence, measurability, law $\mu$); $\xi_0$ is not used. In 5.1 iv) the limits $a,b$ are named parameters (they are unique). 5.3 iii) is written as "there is $c<2(a-b/4)$ with the bracket $\le c$ for all large $n$", which is the strict limsup inequality without a real `limsup` (whose value on an unbounded sequence is a junk value); the division by $1-\alpha_{n+1}$ is meaningful for large $n$, since $1-\alpha_n\sim a\gamma_n>0$.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 3 Assumption 2.2 and Eq. (2.2); p. 6 Assumptions 4.1, 4.2 i); p. 8 Assumptions 5.1, 5.3

import Mathlib
import Definitions.Def_AdamDyn_DecBdd_Algorithm
import Definitions.Def_AdamDyn_DecConv_StochasticModel

open MeasureTheory Filter Topology

namespace AdamDyn.DecBdd

/-- The objective `F(x) = AdamDyn.ConstStep.E f(x, ξ) = ∫ f(x, ξ) dμ(ξ)` of (2.2), p. 3. -/
noncomputable def objective {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (f : AdamDyn.ConstStep.E d → Ξ → ℝ)
    (μ : Measure Ξ) : AdamDyn.ConstStep.E d → ℝ :=
  fun x => ∫ ξ, f x ξ ∂μ

/-- Assumption 2.2 (p. 3) on `f : ℝ^d × Ξ → ℝ`, with `gf x ξ` the gradient `∇f(x, ξ)` in `x`. -/
structure Assumption22 {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (f : AdamDyn.ConstStep.E d → Ξ → ℝ)
    (gf : AdamDyn.ConstStep.E d → Ξ → AdamDyn.ConstStep.E d) (μ : Measure Ξ) : Prop where
  /-- i) for every `x`, `f(x, ·)` is measurable. -/
  meas : ∀ x, Measurable (f x)
  /-- `ξ ↦ ∇f(x, ξ)` is a.e. strongly measurable (a consequence of i)–ii)). -/
  grad_meas : ∀ x, AEStronglyMeasurable (gf x) μ
  /-- ii) for almost every `ξ`, `f(·, ξ)` is continuously differentiable, with gradient `gf · ξ`. -/
  smooth : ∀ᵐ ξ ∂μ, ContDiff ℝ 1 (fun x => f x ξ) ∧ ∀ x, gf x ξ = gradient (fun y => f y ξ) x
  /-- iii) some `x_*` has `E|f(x_*, ξ)| < ∞` and `E‖∇f(x_*, ξ)‖² < ∞`. -/
  moment : ∃ xs : AdamDyn.ConstStep.E d, Integrable (f xs) μ ∧ ∫⁻ ξ, ‖gf xs ξ‖ₑ ^ 2 ∂μ < ⊤
  /-- iv) for every compact `K` there is `L_K > 0` with
  `E‖∇f(x, ξ) - ∇f(y, ξ)‖² ≤ L_K² ‖x - y‖²` on `K`. -/
  locLip : ∀ K : Set (AdamDyn.ConstStep.E d), IsCompact K → ∃ L : ℝ, 0 < L ∧ ∀ x ∈ K, ∀ y ∈ K,
    ∫⁻ ξ, ‖gf x ξ - gf y ξ‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (L ^ 2 * ‖x - y‖ ^ 2)

/-- Assumption 4.2 i) (p. 6) with exponent `p`: for every compact `K`,
`sup_{x ∈ K} AdamDyn.ConstStep.E‖∇f(x, ξ)‖^p < ∞`. -/
def Assumption42i {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (gf : AdamDyn.ConstStep.E d → Ξ → AdamDyn.ConstStep.E d)
    (μ : Measure Ξ) (p : ℝ) : Prop :=
  ∀ K : Set (AdamDyn.ConstStep.E d), IsCompact K → ⨆ x ∈ K, ∫⁻ ξ, ‖gf x ξ‖ₑ ^ p ∂μ < ⊤

/-- Assumption 5.3 (p. 8), for `F = objective f μ`. -/
structure Assumption53 {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (f : AdamDyn.ConstStep.E d → Ξ → ℝ)
    (gf : AdamDyn.ConstStep.E d → Ξ → AdamDyn.ConstStep.E d) (μ : Measure Ξ) (γ α : ℕ → ℝ) (a b : ℝ) : Prop where
  /-- i) `∇F` is Lipschitz continuous. -/
  lip : ∃ L : NNReal, LipschitzWith L (gradient (objective f μ))
  /-- ii) there is `C > 0` with `E‖∇f(x, ξ)‖² ≤ C (1 + F(x))` for all `x`. -/
  growth : ∃ C : ℝ, 0 < C ∧ ∀ x, Integrable (fun ξ => ‖gf x ξ‖ ^ 2) μ ∧
    ∫ ξ, ‖gf x ξ‖ ^ 2 ∂μ ≤ C * (1 + objective f μ x)
  /-- iii) `limsup_n (1/γ_n - ((1 - α_{n+2})/(1 - α_{n+1})) (1/γ_{n+1})) < 2(a - b/4)`,
  written without a real `limsup`. -/
  limsup : ∃ c : ℝ, c < 2 * (a - b / 4) ∧ ∀ᶠ n in atTop,
    1 / γ n - ((1 - α (n + 2)) / (1 - α (n + 1))) * (1 / γ (n + 1)) ≤ c

end AdamDyn.DecBdd


