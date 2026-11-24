-- Prove2me | Definitions.Def_Arxiv0810_5751_Basic
-- name    : Arxiv0810_5751_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T06:40:24.300793+00:00
-- url     : https://prove2.me/theorems/5b788c1f-0705-49f1-9874-c01e4a7c31c6
-- title:
--   Stacked visibilities, circular complex Gaussian noise and white-noise likelihood for SAGE calibration
-- statement:
--   Objects of Sections II-IV of Yatawatta, Zaroubi, de Bruyn, Koopmans and Noordam (2008).
--
--   1. **Stacked data (Section II).** An array has $N$ dual-polarised stations. A baseline is a pair $(p,q)$ with $p<q$; autocorrelations $p=q$ are ignored. For a set $B$ of baselines, the data vector $\mathbf y$ stacks the four entries of $\mathrm{vec}(\mathbf V_{pq})$ of each $2\times2$ visibility matrix $\mathbf V_{pq}$, $(p,q)\in B$; its length $M$ is $4|B|$, the size of the index set $B\times\{1,2\}^2$.
--   2. **Circular complex Gaussian law.** A random vector $\mathbf z\in\mathbb C^\iota$ is zero-mean circular complex Gaussian with covariance $\mathbf C=E\{\mathbf z\mathbf z^H\}$ if $E\exp\big(i\,\mathrm{Re}(\mathbf w^H\mathbf z)\big)=\exp(-\mathbf w^H\mathbf C\mathbf w/4)$ for every $\mathbf w\in\mathbb C^\iota$. For positive definite $\mathbf C$ this is the law with density $(\pi^M|\mathbf C|)^{-1}\exp(-\mathbf z^H\mathbf C^{-1}\mathbf z)$ used in eq. (15).
--   3. **EM noise split (eq. (8)).** For weights $\beta_1,\dots,\beta_K$ and an $M\times M$ covariance $\mathbf\Pi$, the stacked noise components $(\tilde{\mathbf n}_1,\dots,\tilde{\mathbf n}_K)$ have covariance $E\{\tilde{\mathbf n}_i\tilde{\mathbf n}_j^H\}=\beta_i\delta_{ij}\mathbf\Pi$.
--   4. **Residual.** For source contributions $\mathbf s_i:\mathbb C^P\to\mathbb C^M$, $i=1,\dots,K$, and $\boldsymbol\theta\in\mathbb C^P$, the residual is $\mathbf r(\boldsymbol\theta)=\mathbf y-\sum_{i=1}^K\mathbf s_i(\boldsymbol\theta)$ and $\|\mathbf r(\boldsymbol\theta)\|^2=\mathbf r^H\mathbf r$.
--   5. **Likelihood (eqs. (15)-(16)).** $f(\mathbf y\mid\boldsymbol\theta)=(\pi^M|\mathbf\Pi|)^{-1}\exp(-\mathbf r^H\mathbf\Pi^{-1}\mathbf r)$, and for white noise $\mathbf\Pi=\sigma^2\mathbf I$ the log-likelihood is $L(\boldsymbol\theta,\sigma^2)=\log f(\mathbf y\mid\boldsymbol\theta)$.
--   6. **Section IV estimates.** $\widehat{\sigma^2}=\frac1M\mathbf r(\hat{\boldsymbol\theta})^H\mathbf r(\hat{\boldsymbol\theta})$ (eq. (17)); $L(\hat{\boldsymbol\theta})=-M\log\pi-M-M\log\big(\frac1M\mathbf r(\hat{\boldsymbol\theta})^H\mathbf r(\hat{\boldsymbol\theta})\big)$ (eq. (18)); $\mathrm{AIC}(K)=-2L(\hat{\boldsymbol\theta})+2(2P)$ (eq. (19)).
--
--   **Formalization Note** The paper writes $\mathbf n\sim\mathcal N(\mathbf 0,\mathbf\Pi)$ and uses the circular density (15); the definition makes circularity explicit through the characteristic function. The determinant and the quadratic form in (15) are taken as real parts, which they are for Hermitian $\mathbf\Pi$. The covariance is written `Pcov` in Lean.
-- source:
--   Yatawatta, Zaroubi, de Bruyn, Koopmans and Noordam, Radio interferometric calibration using the SAGE algorithm, arXiv:0810.5751v1 (2008), Section II (eqs. (2)-(5)), Section III-A (eq. (8)), Section IV (eqs. (15)-(19)), PDF pp. 2-4

import Mathlib

/-!
Yatawatta, Zaroubi, de Bruyn, Koopmans and Noordam, *Radio interferometric calibration using the
SAGE algorithm*, arXiv:0810.5751v1 (2008), 13th IEEE DSP Workshop (2009): the stacked
cross-correlation data of Section II (eqs. (2)-(4)), the circular complex Gaussian noise model of
Sections II-III (eqs. (4), (8), (15)), and the white-noise likelihood, maximum-likelihood noise
variance, concentrated log-likelihood and Akaike criterion of Section IV (eqs. (5), (15)-(19)).
-/

open MeasureTheory Matrix

noncomputable section

namespace Arxiv0810_5751

/-- Section II, text before eq. (4): the cross-correlation baselines `(p, q)` with `p < q` of an
array of `N` stations (autocorrelations `p = q` are ignored). -/
def crossBaselines (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun b => b.1 < b.2

/-- Section II, eq. (4): the index set of the stacked data vector `y` built from the baselines in
`B`: each baseline `(p, q)` contributes the four entries of `vec(V_pq)`, `V_pq` a `2 × 2` matrix.
The length `M` of `y` is the cardinality of this type. -/
abbrev VisIndex {N : ℕ} (B : Finset (Fin N × Fin N)) : Type :=
  B × (Fin 2 × Fin 2)

/-- Section II, eqs. (2)-(4): the stacked vector `y = [v_12ᵀ v_13ᵀ … v_(N-1)Nᵀ]ᵀ` of the
vectorised visibilities `v_pq = vec(V_pq)` over the baselines in `B`. -/
def stackedVis {N : ℕ} (V : Fin N → Fin N → Matrix (Fin 2) (Fin 2) ℂ)
    (B : Finset (Fin N × Fin N)) : VisIndex B → ℂ :=
  fun x => V x.1.1.1 x.1.1.2 x.2.1 x.2.2

/-- Section II (`n ∼ N(0, Π)`) and eq. (15): `ν` is the law of a zero-mean circular complex
Gaussian vector with covariance `C = E{z zᴴ}`, characterised by its characteristic function
`E exp(i Re(wᴴ z)) = exp(-wᴴ C w / 4)` for all `w`. For positive definite `C` this is the law with
density `(π^M |C|)⁻¹ exp(-zᴴ C⁻¹ z)` of eq. (15). -/
def IsCircGaussian {ι : Type*} [Fintype ι] (ν : Measure (ι → ℂ)) (C : Matrix ι ι ℂ) : Prop :=
  ∀ w : ι → ℂ, ∫ z, Complex.exp (Complex.I * ((star w ⬝ᵥ z).re : ℂ)) ∂ν =
    Complex.exp (-(1 / 4 : ℂ) * (star w ⬝ᵥ C *ᵥ w))

/-- Section III-A, eq. (8): the covariance `E{ñ_i ñ_jᴴ} = β_i δ_ij Π` of the stacked noise
components `(ñ_1, …, ñ_K)`, as a matrix indexed by (component, data entry). -/
def emNoiseCov {K M : ℕ} (β : Fin K → ℝ) (Pcov : Matrix (Fin M) (Fin M) ℂ) :
    Matrix (Fin K × Fin M) (Fin K × Fin M) ℂ :=
  fun a b => if a.1 = b.1 then (β a.1 : ℂ) * Pcov a.2 b.2 else 0

/-- Section II, eqs. (4)-(5): the residual `y - ∑_{i=1}^K s_i(θ)` of the data `y ∈ ℂ^M` for the
source contributions `s_i : ℂ^P → ℂ^M` at the parameter `θ ∈ ℂ^P`. -/
def residual {K M P : ℕ} (y : Fin M → ℂ) (s : Fin K → (Fin P → ℂ) → Fin M → ℂ)
    (θ : Fin P → ℂ) : Fin M → ℂ :=
  y - ∑ i, s i θ

/-- Eqs. (5), (16)-(18): the squared residual norm
`‖y - ∑_i s_i(θ)‖² = (y - ∑_i s_i(θ))ᴴ (y - ∑_i s_i(θ))`. -/
def residSq {K M P : ℕ} (y : Fin M → ℂ) (s : Fin K → (Fin P → ℂ) → Fin M → ℂ)
    (θ : Fin P → ℂ) : ℝ :=
  ∑ m, Complex.normSq (residual y s θ m)

/-- Section IV, eq. (15): the likelihood
`f(y | θ) = (π^M |Π|)⁻¹ exp(-(y - ∑_i s_i(θ))ᴴ Π⁻¹ (y - ∑_i s_i(θ)))` of the observation model (4)
with circular complex Gaussian noise of covariance `Π` (`|Π|` the determinant). -/
def likelihood {K M P : ℕ} (Pcov : Matrix (Fin M) (Fin M) ℂ) (y : Fin M → ℂ)
    (s : Fin K → (Fin P → ℂ) → Fin M → ℂ) (θ : Fin P → ℂ) : ℝ :=
  (Real.pi ^ M * (Pcov.det).re)⁻¹ *
    Real.exp (-(star (residual y s θ) ⬝ᵥ Pcov⁻¹ *ᵥ residual y s θ).re)

/-- Section IV, eq. (16): the log-likelihood `L(θ) = log f(y | θ)` for white noise `Π = σ² I`,
as a function of the noise variance `σ2 = σ²` and the parameter `θ`. -/
def whiteLogLik {K M P : ℕ} (σ2 : ℝ) (y : Fin M → ℂ) (s : Fin K → (Fin P → ℂ) → Fin M → ℂ)
    (θ : Fin P → ℂ) : ℝ :=
  Real.log (likelihood ((σ2 : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)) y s θ)

/-- Section IV, eq. (17): the noise-variance estimate
`σ̂² = (1/M) (y - ∑_i s_i(θ̂))ᴴ (y - ∑_i s_i(θ̂))`. -/
def mlNoiseVar {K M P : ℕ} (y : Fin M → ℂ) (s : Fin K → (Fin P → ℂ) → Fin M → ℂ)
    (θ : Fin P → ℂ) : ℝ :=
  residSq y s θ / M

/-- Section IV, eq. (18): `L(θ̂) = -M log π - M - M log((1/M)(y - ∑_i s_i(θ̂))ᴴ(y - ∑_i s_i(θ̂)))`. -/
def concLogLik {K M P : ℕ} (y : Fin M → ℂ) (s : Fin K → (Fin P → ℂ) → Fin M → ℂ)
    (θ : Fin P → ℂ) : ℝ :=
  -(M : ℝ) * Real.log Real.pi - M - M * Real.log (residSq y s θ / M)

/-- Section IV, eq. (19): Akaike's criterion `AIC(K) = -2 L(θ̂) + 2(2P)` for the model with `K`
sources and `P` complex parameters (`2P` real parameters), with `L(θ̂)` as in eq. (18). -/
def aic {K M P : ℕ} (y : Fin M → ℂ) (s : Fin K → (Fin P → ℂ) → Fin M → ℂ)
    (θ : Fin P → ℂ) : ℝ :=
  -2 * concLogLik y s θ + 2 * (2 * P)

end Arxiv0810_5751


