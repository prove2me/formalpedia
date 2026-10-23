-- Prove2me | Definitions.Def_HerdingForecast_Equilibrium_Model
-- name    : HerdingForecast_Equilibrium_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:18.520643+00:00
-- url     : https://prove2.me/theorems/7d20043a-fba8-4093-b113-aa654b9b1eba
-- title:
--   §2, eqs. (1)–(3), (7)–(11), pp. 8–12 — herding game for normal probabilistic forecasts: flat-prior posterior, log score, KL deviation, objective, equilibrium, closed form
-- statement:
--   This file sets up the herding game of Jia, Keppo and Satopää for normal probabilistic forecasts.
--
--   **Signals.** There are $K \ge 2$ experts forecasting an unknown state $\theta \in \mathbb R$ with the improper flat prior $\pi(\theta) \propto 1$. Expert $k$ observes a public signal $y = \theta + \epsilon_y$ and a private signal $x_k = \theta + \epsilon_{x_k}$, where $\epsilon_y \sim N(0, \tau_y^{-1})$ and $\epsilon_{x_k} \sim N(0, \tau_x^{-1})$ are independent and $\tau_x, \tau_y > 0$ are the precisions. Write
--   $$\hat\theta_k = \frac{\tau_x}{\tau_y+\tau_x}x_k + \frac{\tau_y}{\tau_y+\tau_x}y,\qquad \hat\sigma^2_\theta = (\tau_y+\tau_x)^{-1},\qquad \hat\sigma^2_{x_{-i}} = \hat\sigma^2_\theta + \tau_x^{-1}.$$
--   The **posterior** of $\theta$ given $(x_k, y)$ is defined directly from the model: Lebesgue measure weighted by the likelihood of $(x_k, y)$ at $\theta$ (the product of the two normal densities), normalized to total mass one. The **predictive law** of another expert's private signal $x_j = \theta + \epsilon_{x_j}$ given $(x_k, y)$ is the posterior convolved with $N(0, \tau_x^{-1})$.
--
--   **Forecasts and payoffs.** A forecast is a pair $a = (\mu, \sigma^2)$ with $\sigma^2 > 0$, standing for the normal distribution $N(\mu, \sigma^2)$. Its negative logarithmic score (7) at outcome $\theta$ is
--   $$E(a;\theta) = \frac{(\mu-\theta)^2}{2\sigma^2} + \tfrac12\log\sigma^2 + \tfrac12\log 2\pi,$$
--   and the Kullback–Leibler divergence of p. 11 between forecasts $a_j$ and $a_k$ is
--   $$D_{KL}(a_j, a_k) = \tfrac12\Big[\frac{\sigma_j^2}{\sigma_k^2} + \frac{(\mu_k-\mu_j)^2}{\sigma_k^2} - 1 + \log\sigma_k^2 - \log\sigma_j^2\Big].$$
--   A **strategy profile** assigns to every expert $k$ and signals $(x, y)$ a forecast $s_k(x, y)$. Given $r \in [0,1)$ and the others' strategies, the **objective** (9) of expert $k$ at $(x_k, y)$ when reporting $a$ is
--   $$(1-r)\,\mathbb E[E(a;\theta)\mid x_k, y] + r\,\frac{1}{K-1}\sum_{j\ne k}\mathbb E[D_{KL}(s_j(x_j, y), a)\mid x_k, y],$$
--   the first expectation under the posterior and the second under the predictive law, as in the average deviation (8).
--
--   **Equilibrium.** A profile is **admissible** if each strategy is jointly measurable, reports positive variances, and has integrable mean, squared mean, variance and log-variance under the predictive law at every signal pair. A **(Bayesian Nash) equilibrium** is an admissible profile in which, at every signal pair $(x_k, y)$, expert $k$'s forecast minimizes the objective over all forecasts $(\mu, \sigma^2)$ with $\sigma^2 > 0$.
--
--   **Closed form.** The Morris–Shin mean (10), the coefficients of (11), and the closed-form profile are
--   $$\mu^{MS}_k = \frac{(1-r)\tau_x}{(1-r)\tau_x+\tau_y}x_k + \frac{\tau_y}{(1-r)\tau_x+\tau_y}y,\quad a = \frac{r(1-r)\tau_x^2\tau_y^2}{[(\tau_x+\tau_y)^2 - r\tau_x^2][(1-r)\tau_x+\tau_y]^2},\quad d = \frac{(1+r)\tau_x+\tau_y}{(\tau_x+\tau_y)^2 - r\tau_x^2},$$
--   with every expert reporting $(\mu^{MS}_k, a(x_k-y)^2 + d)$. The right-hand sides of the first-order conditions (EC.11)–(EC.12) are also defined, for an arbitrary profile: $\mu^* = (1-r)\hat\theta_k + r\frac{1}{K-1}\sum_{j\ne k}\mathbb E[\mu_j\mid x_k,y]$ and $v^* = (1-r)\big((\mu^*-\hat\theta_k)^2 + \hat\sigma^2_\theta\big) + r\frac{1}{K-1}\sum_{j\ne k}\mathbb E[(\mu^*-\mu_j)^2 + \sigma_j^2\mid x_k, y]$. Finally, a profile has **polynomially growing variances** if for every expert $k$ and public signal $y$ there are $C$ and $N$ with $\sigma_k^2(x, y) \le C(1+|x|^N)$ for all $x$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The improper prior admits no joint probability measure on $(\theta, y, x_1, \dots, x_K)$, so conditional expectations given $(x_k, y)$ are integrals against the two explicit laws above. Variances are real numbers; Mathlib's Gaussian takes a nonnegative real variance, so $\tau^{-1}$ is converted with `Real.toNNReal`. Logarithms are natural. The standing assumptions $K \ge 2$, $\tau_x, \tau_y > 0$, $0 \le r < 1$ are bundled in `Standing`; the paper allows $r = 1$, which is excluded because uniqueness fails there (every constant profile is an equilibrium) and the paper's proof assumes $r < 1$. The equilibrium requires a best response at every signal pair, not almost every one. Admissibility is the integrability needed for the expectation in (9) to be finite; it is not printed in the paper.
-- source:
--   Jia, Keppo & Satopää, Herding in Probabilistic Forecasts, SSRN 3674961 (PDF sha256 820fb50d…), pp. 8–12, eqs. (1)–(3), (7), (8), (9), (10), (11); p. ec41 (PDF 79), (EC.11)–(EC.12)

import Mathlib

namespace HerdingForecast.Equilibrium

open MeasureTheory ProbabilityTheory

/-- Parameters of the herding game (§2, pp. 8–12): the number of experts `K`, the level of
herding `r`, the precision `τx` of each private signal and the precision `τy` of the public
signal. -/
structure Params where
  K : ℕ
  r : ℝ
  τx : ℝ
  τy : ℝ

/-- Standing assumptions: at least two experts (the average (8) divides by `K - 1`), positive
precisions, and `0 ≤ r < 1` (the paper allows `r ∈ [0, 1]`; `r = 1` is excluded, see the
mission description). -/
def Standing (P : Params) : Prop :=
  2 ≤ P.K ∧ 0 < P.τx ∧ 0 < P.τy ∧ 0 ≤ P.r ∧ P.r < 1

/-- Posterior mean `θ̂k = τx/(τy+τx) xk + τy/(τy+τx) y` of (3), at private signal `x` and
public signal `y`. -/
noncomputable def thetaHat (P : Params) (x y : ℝ) : ℝ :=
  P.τx / (P.τy + P.τx) * x + P.τy / (P.τy + P.τx) * y

/-- Posterior variance `σ̂²θ = (τy + τx)⁻¹` of (3). -/
noncomputable def postVar (P : Params) : ℝ := (P.τy + P.τx)⁻¹

/-- Predictive variance `σ̂²_{x−i} = σ̂²θ + τx⁻¹` of another expert's private signal given
`(xk, y)` (p. ec41). -/
noncomputable def predVar (P : Params) : ℝ := postVar P + P.τx⁻¹

/-- Likelihood of the signals `(xk, y) = (x, y)` at state `θ` under (1)–(2):
`xk ∼ N(θ, τx⁻¹)` and `y ∼ N(θ, τy⁻¹)` independently. -/
noncomputable def likelihood (P : Params) (x y θ : ℝ) : ℝ :=
  gaussianPDFReal θ (P.τx⁻¹).toNNReal x * gaussianPDFReal θ (P.τy⁻¹).toNNReal y

/-- Expert's belief about `θ` given `(xk, y) = (x, y)` under the improper flat prior
`π(θ) ∝ 1`: Lebesgue measure weighted by the likelihood, normalized to total mass one. -/
noncomputable def posterior (P : Params) (x y : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond (volume.withDensity fun θ => ENNReal.ofReal (likelihood P x y θ))
    Set.univ

/-- Law of another expert's private signal `xj = θ + ϵxj` given `(xk, y) = (x, y)`: the
posterior of `θ` convolved with the noise law `N(0, τx⁻¹)`. -/
noncomputable def predictive (P : Params) (x y : ℝ) : Measure ℝ :=
  posterior P x y ∗ gaussianReal 0 (P.τx⁻¹).toNNReal

/-- Negative logarithmic score (7) of the normal forecast `a = (µ, σ²)` at outcome `θ`:
`(µ − θ)²/(2σ²) + ½ log σ² + ½ log 2π`. -/
noncomputable def logScore (a : ℝ × ℝ) (θ : ℝ) : ℝ :=
  (a.1 - θ) ^ 2 / (2 * a.2) + Real.log a.2 / 2 + Real.log (2 * Real.pi) / 2

/-- KL divergence of p. 11 between the normal forecasts `aj = (µj, σ²j)` and `ak = (µk, σ²k)`:
`½ [σ²j/σ²k + (µk − µj)²/σ²k − 1 + log σ²k − log σ²j]`. -/
noncomputable def dKL (aj ak : ℝ × ℝ) : ℝ :=
  (aj.2 / ak.2 + (ak.1 - aj.1) ^ 2 / ak.2 - 1 + Real.log ak.2 - Real.log aj.2) / 2

/-- A strategy profile: `s k x y = (µ, σ²)` is the forecast of expert `k` with private signal
`x` and public signal `y`. -/
abbrev Profile (K : ℕ) := Fin K → ℝ → ℝ → ℝ × ℝ

/-- The objective (9) of expert `k` at signals `(x, y)` when reporting `a`, against the
profile `s` of the others: `(1 − r) E[E(a; θ) | xk, y] + r E[D(a, a−k) | xk, y]`, with the
average deviation (8) over `j ≠ k` with weight `1/(K − 1)`. -/
noncomputable def objective (P : Params) (s : Profile P.K) (k : Fin P.K) (x y : ℝ)
    (a : ℝ × ℝ) : ℝ :=
  (1 - P.r) * ∫ θ, logScore a θ ∂posterior P x y
    + P.r * (1 / ((P.K : ℝ) - 1)) *
      ∑ j ∈ Finset.univ.erase k, ∫ x', dKL (s j x' y) a ∂predictive P x y

/-- Admissible profiles: every strategy is jointly measurable in the signals, reports a
positive variance, and, at every conditioning signal pair, has integrable mean, squared
mean, variance and log-variance under the predictive law, so that the expectation in (9)
is finite. -/
def Admissible (P : Params) (s : Profile P.K) : Prop :=
  ∀ j, Measurable (Function.uncurry (s j)) ∧ (∀ x y, 0 < (s j x y).2) ∧
    ∀ x y, Integrable (fun x' => (s j x' y).1) (predictive P x y) ∧
      Integrable (fun x' => (s j x' y).1 ^ 2) (predictive P x y) ∧
      Integrable (fun x' => (s j x' y).2) (predictive P x y) ∧
      Integrable (fun x' => Real.log (s j x' y).2) (predictive P x y)

/-- Bayesian Nash equilibrium of the game (9): an admissible profile in which every expert's
forecast minimizes the objective at every signal pair, over every normal forecast
`(µ, σ²)` with `σ² > 0`. -/
def IsEquilibrium (P : Params) (s : Profile P.K) : Prop :=
  Admissible P s ∧
    ∀ (k : Fin P.K) (x y : ℝ) (a : ℝ × ℝ), 0 < a.2 →
      objective P s k x y (s k x y) ≤ objective P s k x y a

/-- The Morris–Shin mean (10): `(1 − r)τx/((1 − r)τx + τy) xk + τy/((1 − r)τx + τy) y`. -/
noncomputable def muMS (P : Params) (x y : ℝ) : ℝ :=
  (1 - P.r) * P.τx / ((1 - P.r) * P.τx + P.τy) * x + P.τy / ((1 - P.r) * P.τx + P.τy) * y

/-- The coefficient `a` of (11). -/
noncomputable def aCoef (P : Params) : ℝ :=
  P.r * (1 - P.r) * P.τx ^ 2 * P.τy ^ 2 /
    (((P.τx + P.τy) ^ 2 - P.r * P.τx ^ 2) * ((1 - P.r) * P.τx + P.τy) ^ 2)

/-- The coefficient `d` of (11). -/
noncomputable def dCoef (P : Params) : ℝ :=
  ((1 + P.r) * P.τx + P.τy) / ((P.τx + P.τy) ^ 2 - P.r * P.τx ^ 2)

/-- The closed-form profile of Theorem 1: every expert reports the normal forecast with mean
(10) and variance `a (xk − y)² + d` of (11). -/
noncomputable def closedForm (P : Params) : Profile P.K :=
  fun _ x y => (muMS P x y, aCoef P * (x - y) ^ 2 + dCoef P)

/-- Right-hand side of the first-order condition (EC.11) for the mean of expert `k`. -/
noncomputable def brMean (P : Params) (s : Profile P.K) (k : Fin P.K) (x y : ℝ) : ℝ :=
  (1 - P.r) * thetaHat P x y
    + P.r * (1 / ((P.K : ℝ) - 1)) *
      ∑ j ∈ Finset.univ.erase k, ∫ x', (s j x' y).1 ∂predictive P x y

/-- Right-hand side of the first-order condition (EC.12) for the variance of expert `k`,
with the mean set to `brMean`. -/
noncomputable def brVar (P : Params) (s : Profile P.K) (k : Fin P.K) (x y : ℝ) : ℝ :=
  (1 - P.r) * ((brMean P s k x y - thetaHat P x y) ^ 2 + postVar P)
    + P.r * (1 / ((P.K : ℝ) - 1)) *
      ∑ j ∈ Finset.univ.erase k,
        ∫ x', ((brMean P s k x y - (s j x' y).1) ^ 2 + (s j x' y).2) ∂predictive P x y

/-- Polynomial growth of the reported variances in the private signal, for each expert and
each public signal. -/
def PolyGrowth {K : ℕ} (s : Profile K) : Prop :=
  ∀ (k : Fin K) (y : ℝ), ∃ C : ℝ, ∃ N : ℕ, ∀ x : ℝ, (s k x y).2 ≤ C * (1 + |x| ^ N)

end HerdingForecast.Equilibrium


