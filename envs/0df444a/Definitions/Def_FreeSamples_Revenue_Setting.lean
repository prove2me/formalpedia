-- Prove2me | Definitions.Def_FreeSamples_Revenue_Setting
-- name    : FreeSamples_Revenue_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:08.892983+00:00
-- url     : https://prove2.me/theorems/b9df9df6-243b-464c-993b-83f31b2ce79c
-- title:
--   Sec. 2–4, Prop. 1, (2), Assumption 1 — priors, Brownian data, posterior maps, g_t, the Buyer's U and BR, free-sample policies and revenue
-- statement:
--   This file fixes the model of Drakopoulos and Makhdoumi, *Providing Data Samples for Free*.
--
--   **Parameters.** A Buyer holds the prior $\theta\sim\mathcal N(\theta_0,\sigma_0^2)$ on an unknown real parameter $\theta$. A Seller believes the Buyer's estimate $\theta_0$ is biased by an amount distributed as $\mathcal N(\mu_b,\sigma_b^2)$, so her prior is $\mathcal N(\theta_0+\mu_b,\sigma_s^2)$ with $\sigma_s^2=\sigma_0^2+\sigma_b^2$. Data are a signal with noise variance $\sigma^2$. The standing assumptions are $\sigma_0^2>0$, $\sigma_b^2\ge 0$ and $\sigma^2>0$. All variances are stored as real numbers, and $\mathcal N(m,v)$ always denotes the Gaussian law with mean $m$ and **variance** $v$.
--
--   **Data and information.** On a probability space $(\Omega,P)$, let $\theta$ be a random variable and $(B_t)_{t\ge 0}$ a standard Brownian motion independent of $\theta$. The first $t\ge 0$ samples are the signal
--   $$Y_t=\theta t+\sigma B_t .$$
--   The pair $(P,\theta,B)$ is a *model with prior $\mathcal N(m,v)$* if $P$ is a probability measure, $\theta$ and every $B_t$ are measurable, $\theta$ has law $\mathcal N(m,v)$ under $P$, $B$ is a Brownian motion under $P$, and $\theta$ is independent of the path of $B$. The Seller's measure is the model with prior $\mathcal N(\theta_0+\mu_b,\sigma_s^2)$ and the Buyer's is the model with prior $\mathcal N(\theta_0,\sigma_0^2)$. Both use the same law of the data given $\theta$, which is the concordance of the two probability spaces (Definition 1). The information $\mathcal F_t=\sigma(Y_s: s\le t)$ is the natural filtration of the signal.
--
--   **Posterior maps.** For a prior $\mathcal N(m,v)$, after $t$ samples with $Y_t=y$, the posterior variance and mean are
--   $$v_t=\frac{v\sigma^2}{vt+\sigma^2},\qquad m_t(y)=v_t\Big(\frac{m}{v}+\frac{y}{\sigma^2}\Big).$$
--   The Buyer's posterior is $(\theta_t,\sigma_t^2)$, from $(m,v)=(\theta_0,\sigma_0^2)$. The Seller's is $(\tilde\theta_t,\tilde\sigma_t^2)$, from $(\theta_0+\mu_b,\sigma_s^2)$. The Seller's estimate of the Buyer's misspecification is $g_t=\tilde\theta_t-\theta_t$.
--
--   **The Buyer's value of data.** For a utility $u(a,x)$ of action $a\in\mathbb R$ in state $x$, define
--   $$U(\theta,v)=\max_{a}\ \mathbb E_{\mathcal N(\theta,v)}[u(a,\cdot)],\qquad BR(\theta,v)=\mathbb E_{\mathcal N(\theta,v)}\big[\max_a u(a,\cdot)\big]-U(\theta,v).$$
--   These are well defined under the hypothesis *HasMax*. It says that $a\mapsto u(a,x)$ attains its maximum for every $x$, that $a\mapsto\mathbb E_{\mathcal N(m,v)}[u(a,\cdot)]$ attains its maximum for every $m$ and every $v>0$, and that $u(a,\cdot)$ and $\max_a u(a,\cdot)$ are integrable under every $\mathcal N(m,v)$ with $v>0$. *Assumption 1* says that $U$ and $BR$ are twice continuously differentiable on $\mathbb R\times(0,\infty)$. $F_\theta$, $F_{\theta\theta}$ and $F_{\sigma^2}$ are the partial derivatives in the mean and in the variance. The drift coefficient is
--   $$\tfrac12 F_{\theta\theta}(\theta,v)-F_{\sigma^2}(\theta,v)+\frac{g}{v}F_\theta(\theta,v).$$
--   The *growth hypothesis* on $F$ with variance bound $v_0$ requires constants $C,c$ such that $|F|+|F_\theta|+|F_{\theta\theta}|+|F_{\sigma^2}|\le Ce^{c|\theta|}$ at every $(\theta,v)$ with $0<v\le v_0$.
--
--   **Policies and revenue.** A free-sample policy is a bounded stopping time $T$ of $(\mathcal F_t)$, the amount of data given for free. The Seller's realized revenue is $BR(\theta_T,\sigma_T^2)$, the Bayes risk of the Buyer at the stopping amount, and the expected revenue is its integral under the Seller's measure. Selling in one round is $T=0$, with revenue $BR(\theta_0,\sigma_0^2)$.
--
--   **One signal.** For Lemma 3, a Buyer with belief $\mathcal N(m,v)$ who observes one signal $y\sim\mathcal N(\theta,s)$ has posterior $\mathcal N\big(\frac{sm+vy}{v+s},\frac{vs}{v+s}\big)$, and the signal has marginal law $\mathcal N(m,v+s)$. The most she pays for it is
--   $$p(m,v;s)=\mathbb E_{y\sim\mathcal N(m,v+s)}\Big[U\Big(\tfrac{sm+vy}{v+s},\tfrac{vs}{v+s}\Big)\Big]-U(m,v).$$
--
--   **Formalization Note.** Variances are reals passed to Mathlib's `gaussianReal` through `toNNReal`. The filtration is the natural filtration of $Y$ without augmentation by null sets. The paper requires only that $T$ be measurable with respect to the information; boundedness of $T$, Assumption 1 read as $C^2$, the HasMax hypothesis and the growth hypothesis are pins that rule out Lean's junk value $0$ for non-integrable integrals and unbounded suprema.
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, pp. 7–16, Sec. 2.1–2.3, Definition 1, Proposition 1, (2), p. 14 (U, BR), Assumption 1 (p. 15), Sec. 4 (i)–(ii) (p. 16), proof of Lemma 3 (p. 30)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace FreeSamples.Revenue

/-- The primitive parameters of the model (Sec. 2.1–2.3, pp. 7–10): the Buyer's prior mean `θ₀`,
the mean `μb` of the Seller's believed bias, the Buyer's prior variance `σ₀sq = σ₀²`, the variance
`σbsq = σ_b²` of the bias, and the noise variance `σsq = σ²` of the data signal. -/
structure Params where
  θ₀ : ℝ
  μb : ℝ
  σ₀sq : ℝ
  σbsq : ℝ
  σsq : ℝ
  σ₀sq_pos : 0 < σ₀sq
  σbsq_nonneg : 0 ≤ σbsq
  σsq_pos : 0 < σsq

/-- The Seller's prior variance `σ_s² = σ₀² + σ_b²` (p. 10). -/
def Params.σssq (p : Params) : ℝ := p.σ₀sq + p.σbsq

/-- The Gaussian law `N(m, v)` on `ℝ`, parametrized by its mean and its **variance**. -/
noncomputable def N (m v : ℝ) : Measure ℝ := gaussianReal m v.toNNReal

/-- Posterior variance after `t` samples from the prior variance `v`, with noise variance `σsq`
(Proposition 1, p. 13): `v σ² / (v t + σ²)`. -/
noncomputable def postVar (σsq v t : ℝ) : ℝ := v * σsq / (v * t + σsq)

/-- Posterior mean after `t` samples with cumulative signal value `y`, from the prior `N(m, v)`
(Proposition 1, p. 13): `(σ_t²/v) m + (σ_t²/σ²) y`. -/
noncomputable def postMean (σsq m v t y : ℝ) : ℝ := postVar σsq v t * (m / v + y / σsq)

/-- The Buyer's posterior variance `σ_t²`. -/
noncomputable def Params.buyerVar (p : Params) (t : ℝ) : ℝ := postVar p.σsq p.σ₀sq t

/-- The Buyer's posterior mean `θ_t` as a function of `t` and of the signal value `Y_t = y`. -/
noncomputable def Params.buyerMean (p : Params) (t y : ℝ) : ℝ := postMean p.σsq p.θ₀ p.σ₀sq t y

/-- The Seller's posterior variance `σ̃_t²`. -/
noncomputable def Params.sellerVar (p : Params) (t : ℝ) : ℝ := postVar p.σsq p.σssq t

/-- The Seller's posterior mean `θ̃_t` as a function of `t` and of `Y_t = y`. -/
noncomputable def Params.sellerMean (p : Params) (t y : ℝ) : ℝ :=
  postMean p.σsq (p.θ₀ + p.μb) p.σssq t y

/-- The Seller's estimate of the Buyer's misspecification, `g_t = θ̃_t − θ_t` (p. 13). -/
noncomputable def Params.gMis (p : Params) (t y : ℝ) : ℝ := p.sellerMean t y - p.buyerMean t y

/-- The data signal `Y_t = θ t + σ B_t` (Sec. 2.2, p. 9), with `σ = √σsq`. -/
noncomputable def Y (σsq : ℝ) {Ω : Type*} (θ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  θ ω * (t : ℝ) + Real.sqrt σsq * B t ω

/-- The probabilistic model on `Ω` under the measure `P`: `θ ~ N(m, v)`, `B` is a standard
Brownian motion, and `B` is independent of `θ`. The Seller's measure is the instance
`(m, v) = (θ₀ + μb, σ_s²)`, the Buyer's is `(θ₀, σ₀²)`; both use the same signal `Y` given `θ`,
which is the concordance of Definition 1 (p. 10). -/
structure IsModel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (m v : ℝ) (θ : Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) : Prop where
  isProb : IsProbabilityMeasure P
  meas_θ : Measurable θ
  meas_B : ∀ t, Measurable (B t)
  law_θ : P.map θ = N m v
  brownian : IsBrownianReal B P
  indep : IndepFun θ (fun ω t => B t ω) P

/-- The information filtration `ℱ_t = σ(Y_s : s ≤ t)`, the natural filtration of the signal
(p. 13), without augmentation by null sets. -/
noncomputable def dataFiltration (σsq : ℝ) {Ω : Type*} [MeasurableSpace Ω] (θ : Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hθ : Measurable θ) (hB : ∀ t, Measurable (B t)) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) :=
  Filtration.natural (Y σsq θ B)
    (fun t => ((hθ.mul_const _).add ((hB t).const_mul _)).stronglyMeasurable)

/-- Standing hypothesis that the maxima in `U` and `BR` (p. 14) exist: for each state `x` the map
`a ↦ u(a, x)` attains its maximum; under every Gaussian `N(m, v)` with `v > 0` the expected utility
`a ↦ E[u(a, ·)]` attains its maximum; and all these expectations are of integrable functions. -/
structure HasMax (u : ℝ → ℝ → ℝ) : Prop where
  pointwise : ∀ x, ∃ a, ∀ a', u a' x ≤ u a x
  integrable : ∀ m v, 0 < v → ∀ a, Integrable (u a) (N m v)
  integrable_max : ∀ m v, 0 < v → Integrable (fun x => ⨆ a, u a x) (N m v)
  expected : ∀ m v, 0 < v → ∃ a, ∀ a', ∫ x, u a' x ∂N m v ≤ ∫ x, u a x ∂N m v

/-- The Buyer's optimal expected utility `U(θ, v) = max_a E_{N(θ,v)}[u(a, ·)]` (p. 14). -/
noncomputable def Uval (u : ℝ → ℝ → ℝ) (θ v : ℝ) : ℝ := ⨆ a, ∫ x, u a x ∂N θ v

/-- The Buyer's Bayes risk `BR(θ, v) = E_{N(θ,v)}[max_a u(a, ·)] − U(θ, v)` (p. 14). Its second
argument is the **variance**. -/
noncomputable def BR (u : ℝ → ℝ → ℝ) (θ v : ℝ) : ℝ := (∫ x, (⨆ a, u a x) ∂N θ v) - Uval u θ v

/-- Assumption 1 (p. 15), read as `C²` on `ℝ × (0, ∞)`: `U` and `BR` are twice continuously
differentiable in `(θ, σ²)`. -/
def Assumption1 (u : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 (Function.uncurry (Uval u)) (Set.univ ×ˢ Set.Ioi 0) ∧
    ContDiffOn ℝ 2 (Function.uncurry (BR u)) (Set.univ ×ˢ Set.Ioi 0)

/-- `F_θ`, the first partial derivative in `θ`. -/
noncomputable def dθ (F : ℝ → ℝ → ℝ) (θ v : ℝ) : ℝ := deriv (fun x => F x v) θ

/-- `F_θθ`, the second partial derivative in `θ`. -/
noncomputable def dθθ (F : ℝ → ℝ → ℝ) (θ v : ℝ) : ℝ :=
  deriv (fun x => deriv (fun y => F y v) x) θ

/-- `F_{σ²}`, the first partial derivative in the variance argument. -/
noncomputable def dv (F : ℝ → ℝ → ℝ) (θ v : ℝ) : ℝ := deriv (fun w => F θ w) v

/-- The Seller-side drift coefficient `½ F_θθ − F_{σ²} + (g/v) F_θ` at `(θ, v)` with
misspecification `g` (Lemma 4(b), Theorem 1, pp. 17–18). -/
noncomputable def drift (F : ℝ → ℝ → ℝ) (θ v g : ℝ) : ℝ :=
  (1 / 2) * dθθ F θ v - dv F θ v + g / v * dθ F θ v

/-- Growth hypothesis (a disclosed integrability pin): `F` and its partial derivatives
`F_θ, F_θθ, F_{σ²}` grow at most exponentially in `|θ|`, uniformly over variances in `(0, v₀]`. -/
def GrowthPin (F : ℝ → ℝ → ℝ) (v₀ : ℝ) : Prop :=
  ∃ C c : ℝ, ∀ θ, ∀ v ∈ Set.Ioc 0 v₀,
    |F θ v| + |dθ F θ v| + |dθθ F θ v| + |dv F θ v| ≤ C * Real.exp (c * |θ|)

/-- A free-sample policy (Sec. 4, p. 16): a stopping amount `T` of free data that is a stopping
time of the information filtration, and is bounded. -/
def IsFreeSamplePolicy {Ω : Type*} [MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (T : Ω → ℝ≥0) : Prop :=
  IsStoppingTime ℱ (fun ω => ((T ω : ℝ≥0) : WithTop ℝ≥0)) ∧ ∃ M : ℝ≥0, ∀ ω, T ω ≤ M

/-- The Seller's realized revenue of the free-sample policy `T` (Sec. 4 and Lemma 3, p. 16): the
Buyer's Bayes risk `BR(θ_T, σ_T²)` at the stopping amount, where `θ_T` and `σ_T²` are the Buyer's
posterior mean and variance after `T` samples. Expected revenue is its integral under the
Seller's measure. -/
noncomputable def revenue (p : Params) (u : ℝ → ℝ → ℝ) {Ω : Type*} (θ : Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (ω : Ω) : ℝ :=
  BR u (p.buyerMean (T ω) (Y p.σsq θ B (T ω) ω)) (p.buyerVar (T ω))

/-- Posterior mean of `θ ~ N(m, v)` after observing one signal `y` of `N(θ, s)` (Lemma 3's
proof, p. 30): `(s m + v y)/(v + s)`. At `s = 0` the signal is `θ` itself and this is `y`. -/
noncomputable def sigPostMean (m v s y : ℝ) : ℝ := (s * m + v * y) / (v + s)

/-- Posterior variance after one signal of noise variance `s`: `v s / (v + s)`. -/
noncomputable def sigPostVar (v s : ℝ) : ℝ := v * s / (v + s)

/-- The most the Buyer with belief `N(m, v)` pays for a signal `Y ~ N(θ, s)` (Lemma 3's proof,
p. 30): `E[max_a E[u(a, θ) | Y]] − max_a E[u(a, θ)]`, where `Y` has marginal law `N(m, v + s)`. -/
noncomputable def signalPrice (u : ℝ → ℝ → ℝ) (m v s : ℝ) : ℝ :=
  (∫ y, Uval u (sigPostMean m v s y) (sigPostVar v s) ∂N m (v + s)) - Uval u m v

end FreeSamples.Revenue


