-- Prove2me | Definitions.Def_AdamDyn_DecConv_StochasticModel
-- name    : AdamDyn_DecConv_StochasticModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:08.937142+00:00
-- url     : https://prove2.me/theorems/841538b6-4c1c-44d8-9289-e7d9a0e2201a
-- title:
--   The critical set $\mathcal S$ of $F$ and Assumptions 2.2, 4.1, 4.2 i), 5.1 of the decreasing-step model
-- statement:
--   Let $\Xi$ be a measurable space, $\mu$ the law of the random variable $\xi$ on $\Xi$, $f : \mathbb R^d \times \Xi \to \mathbb R$ an integrand and $\nabla f(x, \xi)$ its gradient in $x$, given as a map $g_f : \mathbb R^d \times \Xi \to \mathbb R^d$.
--
--   1. The objective and the second-moment map of (2.2), declared in the imported constant-step model (`AdamDyn.ConstStep.objective`, `AdamDyn.ConstStep.sqGradMean`), are
--   $$ F(x) = \mathbb E\, f(x, \xi) = \int_\Xi f(x, \xi)\, \mu(d\xi), \qquad S(x) = \mathbb E\big(\nabla f(x, \xi)^{\odot 2}\big), $$
--   the square coordinatewise. The **critical set** is $\mathcal S = \nabla F^{-1}(\{0\})$.
--   2. **Assumption 2.2.** i) $f(x, \cdot)$ is measurable for every $x$ (and $\nabla f(x, \cdot)$ is a.e. strongly measurable); ii) for $\mu$-almost every $\xi$, $f(\cdot, \xi)$ is continuously differentiable with gradient $\nabla f(\cdot, \xi)$; iii) some $x_*$ has $\mathbb E|f(x_*, \xi)| < \infty$ and $\mathbb E\|\nabla f(x_*, \xi)\|^2 < \infty$; iv) for every compact $K$ there is $L_K > 0$ with $\mathbb E\|\nabla f(x, \xi) - \nabla f(y, \xi)\|^2 \le L_K^2 \|x - y\|^2$ for all $x, y \in K$.
--   3. **Assumption 4.1.** The samples $(\xi_n : n \ge 1)$, random variables on a probability space $(\Omega, \mathcal F, \mathbb P)$, are independent and identically distributed with law $\mu$.
--   4. **Assumption 4.2 i)** with exponent $p$: for every compact $K$, $\sup_{x \in K} \mathbb E\|\nabla f(x, \xi)\|^p < \infty$.
--   5. **Assumption 5.1 (stepsizes).** i) $\gamma_n > 0$ for all $n \in \mathbb N$ and $\gamma_{n+1}/\gamma_n \to 1$; ii) $\sum_n \gamma_n = +\infty$ and $\sum_n \gamma_n^2 < +\infty$; iii) $0 \le \alpha_n \le 1$ and $0 \le \beta_n \le 1$ for all $n$; iv) there are $a, b$ with $0 < b < 4a$, $\gamma_n^{-1}(1 - \alpha_n) \to a$ and $\gamma_n^{-1}(1 - \beta_n) \to b$.
--
--   These are the standing hypotheses of the almost-sure convergence theorem for decreasing-step Adam (Theorem 5.2). Under Assumption 2.2, $F$ is continuously differentiable with $\nabla F(x) = \mathbb E \nabla f(x, \xi)$, and $\nabla F$ and $S$ are locally Lipschitz (p. 3).
--
--   **Formalization Note** $F$ and $S$ are Bochner integrals; Assumption 2.2 iii)–iv) make $\xi \mapsto f(x, \xi)$ and $\xi \mapsto \|\nabla f(x,\xi)\|^2$ integrable for every $x$, so these integrals are the true expectations. Moments in Assumptions 2.2 and 4.2 i) are lower Lebesgue integrals in $[0, \infty]$. $\sum_n \gamma_n = +\infty$ is written as divergence of the partial sums to $+\infty$. The index $0$ of $(\xi_n)$ is unused.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 3 (Eq. (2.2), Assumption 2.2, the critical set), p. 6 (Assumptions 4.1, 4.2 i)), p. 8 (Assumption 5.1)

import Mathlib
import Definitions.Def_AdamDyn_DecConv_ODEInf
import Definitions.Def_AdamDyn_ConstStep_StochasticModel

open MeasureTheory Filter Topology

namespace AdamDyn.DecConv

/-- The set of critical points `𝒮 = ∇F⁻¹({0})` of `F` (p. 3). -/
def criticalSet {d : ℕ} (F : AdamDyn.WellPosed.Vec d → ℝ) : Set (AdamDyn.WellPosed.Vec d) :=
  {x | gradient F x = 0}

/-- Assumption 2.2 (p. 3) on `f : ℝ^d × Ξ → ℝ`, with `gf x ξ` the gradient `∇f(x, ξ)` in `x`. -/
structure Assumption22 {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (f : AdamDyn.WellPosed.Vec d → Ξ → ℝ) (gf : AdamDyn.WellPosed.Vec d → Ξ → AdamDyn.WellPosed.Vec d) : Prop where
  /-- i) for every `x`, `f(x, ·)` is measurable. -/
  meas : ∀ x, Measurable (f x)
  /-- `ξ ↦ ∇f(x, ξ)` is a.e. strongly measurable (a consequence of i)–ii), needed to integrate it). -/
  grad_meas : ∀ x, AEStronglyMeasurable (gf x) μ
  /-- ii) for almost every `ξ`, `f(·, ξ)` is continuously differentiable, with gradient `gf · ξ`. -/
  smooth : ∀ᵐ ξ ∂μ, ContDiff ℝ 1 (fun x => f x ξ) ∧ ∀ x, gf x ξ = gradient (fun y => f y ξ) x
  /-- iii) some `x_*` has `E|f(x_*, ξ)| < ∞` and `E‖∇f(x_*, ξ)‖² < ∞`. -/
  moment : ∃ xs : AdamDyn.WellPosed.Vec d, Integrable (f xs) μ ∧ ∫⁻ ξ, ‖gf xs ξ‖ₑ ^ 2 ∂μ < ⊤
  /-- iv) for every compact `K` there is `L_K > 0` with
  `E‖∇f(x, ξ) - ∇f(y, ξ)‖² ≤ L_K² ‖x - y‖²` on `K`. -/
  locLip : ∀ K : Set (AdamDyn.WellPosed.Vec d), IsCompact K → ∃ L : ℝ, 0 < L ∧ ∀ x ∈ K, ∀ y ∈ K,
    ∫⁻ ξ, ‖gf x ξ - gf y ξ‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (L ^ 2 * ‖x - y‖ ^ 2)

/-- Assumption 4.1 (p. 6): the samples `(ξ_n : n ≥ 1)` are iid with the law `μ` of `ξ`
(`ξ 0` is unused). -/
structure Assumption41 {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] (P : Measure Ω)
    (μ : Measure Ξ) (ξ : ℕ → Ω → Ξ) : Prop where
  meas : ∀ n, Measurable (ξ (n + 1))
  indep : ProbabilityTheory.iIndepFun (fun n => ξ (n + 1)) P
  law : ∀ n, P.map (ξ (n + 1)) = μ

/-- Assumption 4.2 i) (p. 6) with exponent `p`: for every compact `K`,
`sup_{x ∈ K} E‖∇f(x, ξ)‖^p < ∞` (moments as lower Lebesgue integrals in `[0, ∞]`). -/
def Assumption42i {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (gf : AdamDyn.WellPosed.Vec d → Ξ → AdamDyn.WellPosed.Vec d) (p : ℝ) : Prop :=
  ∀ K : Set (AdamDyn.WellPosed.Vec d), IsCompact K → (⨆ x ∈ K, ∫⁻ ξ, ‖gf x ξ‖ₑ ^ p ∂μ) < ⊤

/-- Assumption 5.1 (Stepsizes, p. 8), with the limits `a`, `b` of iv) named. -/
structure Assumption51 (γ α β : ℕ → ℝ) (a b : ℝ) : Prop where
  /-- i) `γ_n > 0` for all `n ∈ ℕ`, and `γ_{n+1}/γ_n → 1`. -/
  γ_pos : ∀ n, 0 < γ n
  γ_ratio : Tendsto (fun n => γ (n + 1) / γ n) atTop (𝓝 1)
  /-- ii) `Σ γ_n = +∞` and `Σ γ_n² < +∞`. -/
  γ_sum : Tendsto (fun N => ∑ n ∈ Finset.range N, γ n) atTop atTop
  γ_sq : Summable (fun n => γ n ^ 2)
  /-- iii) `0 ≤ α_n ≤ 1` and `0 ≤ β_n ≤ 1` for all `n`. -/
  α_mem : ∀ n, 0 ≤ α n ∧ α n ≤ 1
  β_mem : ∀ n, 0 ≤ β n ∧ β n ≤ 1
  /-- iv) `0 < b < 4a`, `γ_n⁻¹(1 - α_n) → a`, `γ_n⁻¹(1 - β_n) → b`. -/
  b_pos : 0 < b
  b_lt : b < 4 * a
  α_lim : Tendsto (fun n => (1 - α n) / γ n) atTop (𝓝 a)
  β_lim : Tendsto (fun n => (1 - β n) / γ n) atTop (𝓝 b)

end AdamDyn.DecConv


