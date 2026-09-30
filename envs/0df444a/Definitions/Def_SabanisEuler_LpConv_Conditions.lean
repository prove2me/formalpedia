-- Prove2me | Definitions.Def_SabanisEuler_LpConv_Conditions
-- name    : SabanisEuler_LpConv_Conditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T00:03:41.739293+00:00
-- url     : https://prove2.me/theorems/30b877e1-9b4f-4478-8170-efd16012723c
-- title:
--   Conditions A-1–A-5 on (2.1) and B-1–B-3 on the scheme coefficients
-- statement:
--   The standing conditions of Sabanis (2016), §2, on the coefficients $b:[0,\infty)\times\mathbb R^d\to\mathbb R^d$, $\sigma:[0,\infty)\times\mathbb R^d\to\mathbb R^{d\times d_1}$ of the SDE (2.1), on the coefficient sequences $b_n,\sigma_n$ of the scheme (2.2), and on the initial value $X(0)=\xi$. Here $p_0,p_1\ge2$, $T>0$, $xy$ is the scalar product and $|\cdot|$ the Euclidean (resp. Hilbert–Schmidt) norm.
--
--   1. **A-1.** $x\mapsto b(t,x)$ is continuous for every $t\in[0,T]$.
--   2. **A-2.** For every $R\ge0$ there is a constant $N_R$ with $\sup_{|x|\le R}|b(t,x)|\le N_R$ for all $t\in[0,T]$.
--   3. **A-3.** For every $R>0$ there is $L_R>0$ such that for all $t\in[0,T]$ and $|x|,|y|\le R$,
--   $$2(x-y)(b(t,x)-b(t,y))+(p_1-1)|\sigma(t,x)-\sigma(t,y)|^2\le L_R|x-y|^2.$$
--   4. **A-4.** There is $K>0$ with $2xb(t,x)+(p_0-1)|\sigma(t,x)|^2\le K(1+|x|^2)$ for all $t\in[0,T]$, $x\in\mathbb R^d$.
--   5. **A-5.** $\mathbb E[|X(0)|^{p_0}]<\infty$.
--   6. **B-1.** For every $R\ge0$,
--   $$\int_0^T\sup_{|x|\le R}\big[|b_n(t,x)-b(t,x)|^{p_0}+|\sigma_n(t,x)-\sigma(t,x)|^{p_0}\big]\,dt\to0\qquad(n\to\infty).$$
--   7. **B-2** (for a given $\alpha$). There is a constant $C$ such that for every $n\ge1$, $t\in[0,T]$, $x\in\mathbb R^d$,
--   $$|b_n(t,x)|\le\min\big(Cn^{\alpha}(1+|x|),|b(t,x)|\big),\qquad|\sigma_n(t,x)|^2\le\min\big(Cn^{\alpha}(1+|x|^2),|\sigma(t,x)|^2\big).$$
--   8. **B-3.** There is $K>0$ such that for every $n\ge1$, $t\in[0,T]$, $x\in\mathbb R^d$, $2xb_n(t,x)+(p_0-1)|\sigma_n(t,x)|^2\le K(1+|x|^2)$.
--
--   A-1–A-5 are local monotonicity, coercivity and moment conditions on the SDE; B-1–B-3 say that the scheme's coefficients approximate $b,\sigma$ locally in $L^{p_0}(dt)$, grow at most like $n^\alpha$ times a linear function while never exceeding the original coefficients, and satisfy the coercivity condition uniformly in $n$.
--
--   **Formalization Note** Each condition is a separate proposition carrying its own existential constant (the two $K$'s of A-4 and B-3 are unrelated). Expectations and the integral in B-1 are computed in $[0,\infty]$; B-1 also requires its integrand (a supremum over an uncountable ball) to be almost everywhere measurable in $t$ for every $n\ge1$, which the paper's Lebesgue integral presupposes. The range $\alpha\in(0,1/2]$ of B-2 is imposed by the theorems that use it.
-- source:
--   Sabanis, Euler approximations with varying coefficients, arXiv:1308.1796v4, pp. 3-4, conditions A-1–A-5 and B-1–B-3, eqs. (2.3)–(2.5)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open SabanisEuler.Shared

namespace SabanisEuler.LpConv

open EthierKurtz

variable {d d₁ : ℕ}

/-- Sabanis (2016), p. 3, A-1: `b(t, x)` is continuous in `x` for every `t ∈ [0, T]`. -/
def CondA1 (T : ℝ≥0) (b : ℝ≥0 × SDEState d → SDEState d) : Prop :=
  ∀ t ≤ T, Continuous (fun x => b (t, x))

/-- Sabanis (2016), p. 3, A-2: for every `R ≥ 0` there is a constant `N_R` with
`sup_{|x| ≤ R} |b(t, x)| ≤ N_R` for all `t ∈ [0, T]`. -/
def CondA2 (T : ℝ≥0) (b : ℝ≥0 × SDEState d → SDEState d) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∃ N : ℝ, ∀ t ≤ T, ∀ x : SDEState d, ‖x‖ ≤ R → ‖b (t, x)‖ ≤ N

/-- Sabanis (2016), p. 3, A-3 (local monotonicity): for every `R > 0` there is `L_R > 0`
with `2 (x - y)·(b(t, x) - b(t, y)) + (p₁ - 1) |σ(t, x) - σ(t, y)|² ≤ L_R |x - y|²` for all
`t ∈ [0, T]` and `|x|, |y| ≤ R`. -/
def CondA3 (T : ℝ≥0) (p₁ : ℝ) (b : ℝ≥0 × SDEState d → SDEState d)
    (σ : ℝ≥0 × SDEState d → Diffusion d d₁) : Prop :=
  ∀ R : ℝ, 0 < R → ∃ L : ℝ, 0 < L ∧ ∀ t ≤ T, ∀ x y : SDEState d, ‖x‖ ≤ R → ‖y‖ ≤ R →
    2 * inner ℝ (x - y) (b (t, x) - b (t, y)) + (p₁ - 1) * ‖σ (t, x) - σ (t, y)‖ ^ 2
      ≤ L * ‖x - y‖ ^ 2

/-- Sabanis (2016), p. 3, A-4 (coercivity): there is `K > 0` with
`2 x·b(t, x) + (p₀ - 1) |σ(t, x)|² ≤ K (1 + |x|²)` for all `t ∈ [0, T]`, `x ∈ ℝ^d`. -/
def CondA4 (T : ℝ≥0) (p₀ : ℝ) (b : ℝ≥0 × SDEState d → SDEState d)
    (σ : ℝ≥0 × SDEState d → Diffusion d d₁) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ t ≤ T, ∀ x : SDEState d,
    2 * inner ℝ x (b (t, x)) + (p₀ - 1) * ‖σ (t, x)‖ ^ 2 ≤ K * (1 + ‖x‖ ^ 2)

/-- Sabanis (2016), p. 3, A-5: `𝔼[|X(0)|^{p₀}] < ∞` (expectation as a lower Lebesgue
integral in `[0, ∞]`). -/
def CondA5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (p₀ : ℝ) (ξ : Ω → SDEState d) :
    Prop :=
  ∫⁻ ω, ‖ξ ω‖ₑ ^ p₀ ∂P < ⊤

/-- Sabanis (2016), p. 3, B-1, eq. (2.3): for every `R ≥ 0`,
`∫₀ᵀ sup_{|x| ≤ R} [|bₙ(t, x) - b(t, x)|^{p₀} + |σₙ(t, x) - σ(t, x)|^{p₀}] dt → 0` as
`n → ∞`. The integrand is computed in `[0, ∞]`, and (as the paper's Lebesgue integral
presupposes) it is required to be a.e.-measurable on `[0, T]` for every `n ≥ 1`. -/
def CondB1 (T : ℝ≥0) (p₀ : ℝ) (b : ℝ≥0 × SDEState d → SDEState d)
    (σ : ℝ≥0 × SDEState d → Diffusion d d₁) (bₙ : ℕ → ℝ≥0 × SDEState d → SDEState d)
    (σₙ : ℕ → ℝ≥0 × SDEState d → Diffusion d d₁) : Prop :=
  ∀ R : ℝ, 0 ≤ R →
    (∀ n : ℕ, 1 ≤ n → AEMeasurable
      (fun t : ℝ => ⨆ x ∈ Metric.closedBall (0 : SDEState d) R,
        (‖bₙ n (t.toNNReal, x) - b (t.toNNReal, x)‖ₑ ^ p₀ +
          ‖σₙ n (t.toNNReal, x) - σ (t.toNNReal, x)‖ₑ ^ p₀))
      (volume.restrict (Set.Icc (0 : ℝ) T))) ∧
    Tendsto (fun n : ℕ => ∫⁻ t in Set.Icc (0 : ℝ) T,
      ⨆ x ∈ Metric.closedBall (0 : SDEState d) R,
        (‖bₙ n (t.toNNReal, x) - b (t.toNNReal, x)‖ₑ ^ p₀ +
          ‖σₙ n (t.toNNReal, x) - σ (t.toNNReal, x)‖ₑ ^ p₀)) atTop (𝓝 0)

/-- Sabanis (2016), p. 3, B-2, eq. (2.4), for a given exponent `α`: there is a constant `C`
such that for every `n ≥ 1`, `t ∈ [0, T]`, `x ∈ ℝ^d`,
`|bₙ(t, x)| ≤ min(C n^α (1 + |x|), |b(t, x)|)` and
`|σₙ(t, x)|² ≤ min(C n^α (1 + |x|²), |σ(t, x)|²)`.
The range `α ∈ (0, 1/2]` is imposed by the theorems that use this condition. -/
def CondB2 (T : ℝ≥0) (α : ℝ) (b : ℝ≥0 × SDEState d → SDEState d)
    (σ : ℝ≥0 × SDEState d → Diffusion d d₁) (bₙ : ℕ → ℝ≥0 × SDEState d → SDEState d)
    (σₙ : ℕ → ℝ≥0 × SDEState d → Diffusion d d₁) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ t ≤ T, ∀ x : SDEState d,
    ‖bₙ n (t, x)‖ ≤ min (C * (n : ℝ) ^ α * (1 + ‖x‖)) ‖b (t, x)‖ ∧
    ‖σₙ n (t, x)‖ ^ 2 ≤ min (C * (n : ℝ) ^ α * (1 + ‖x‖ ^ 2)) (‖σ (t, x)‖ ^ 2)

/-- Sabanis (2016), p. 4, B-3, eq. (2.5): there is `K > 0` such that for every `n ≥ 1`,
`2 x·bₙ(t, x) + (p₀ - 1) |σₙ(t, x)|² ≤ K (1 + |x|²)` for all `t ∈ [0, T]`, `x ∈ ℝ^d`. -/
def CondB3 (T : ℝ≥0) (p₀ : ℝ) (bₙ : ℕ → ℝ≥0 × SDEState d → SDEState d)
    (σₙ : ℕ → ℝ≥0 × SDEState d → Diffusion d d₁) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n → ∀ t ≤ T, ∀ x : SDEState d,
    2 * inner ℝ x (bₙ n (t, x)) + (p₀ - 1) * ‖σₙ n (t, x)‖ ^ 2 ≤ K * (1 + ‖x‖ ^ 2)

end SabanisEuler.LpConv


