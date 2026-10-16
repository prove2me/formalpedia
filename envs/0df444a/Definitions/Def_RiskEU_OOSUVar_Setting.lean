-- Prove2me | Definitions.Def_RiskEU_OOSUVar_Setting
-- name    : RiskEU_OOSUVar_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:26.921922+00:00
-- url     : https://prove2.me/theorems/1774ad95-39c4-4105-a58b-43a201a545cf
-- title:
--   §3, pp. 9–13 — the market (µ, Σ, γ), σ²_g, µ_g, ψ² (5)–(7), the sample estimators (9), the shrinkage portfolio ŵ*(κ) (10)–(11), OOSU (12), and the closed forms (14)–(19)
-- statement:
--   This file fixes the model of Lassance, Martín-Utrera and Simaan (§3) and the closed-form expressions of their Proposition 1.
--
--   **Market.** There are $N$ stocks whose excess returns have mean vector $\mu\in\mathbb R^N$ and covariance matrix $\Sigma\in\mathbb R^{N\times N}$; the investor has risk-aversion coefficient $\gamma$. The *standing assumptions* for a sample size $T$ are Assumption 1 ($N\ge 2$ and $T>N+7$), $\Sigma$ positive definite, and $\gamma>0$. With $e$ the vector of ones, the population constants are computed from $\mu$ and $\Sigma$ by (5)–(7):
--
--   $$\sigma_g^2=(e^\top\Sigma^{-1}e)^{-1},\qquad \mu_g=\mu^\top\Sigma^{-1}e\,(e^\top\Sigma^{-1}e)^{-1},\qquad \psi^2=\mu^\top\Sigma^{-1}\mu-\mu_g^2/\sigma_g^2,$$
--
--   together with the GMV portfolio $w_g=\Sigma^{-1}e(e^\top\Sigma^{-1}e)^{-1}$ (3) and the matrix $\mathbf B=\Sigma^{-1}(I-e\,w_g^\top)$ (4). The out-of-sample utility of a weight vector $w$ is $U(w)=w^\top\mu-\frac{\gamma}{2}w^\top\Sigma w$ (12), always evaluated at the population $\mu,\Sigma$.
--
--   **Sample.** For returns $r_1,\dots,r_T$, the sample mean and the sample covariance (normalised by $1/T$) are
--
--   $$\hat\mu=\frac1T\sum_{t=1}^T r_t,\qquad \hat\Sigma=\frac1T\sum_{t=1}^T(r_t-\hat\mu)(r_t-\hat\mu)^\top \quad(9).$$
--
--   The sample GMV portfolio is $\hat w_g=\hat\Sigma^{-1}e(e^\top\hat\Sigma^{-1}e)^{-1}$, the sample zero-cost portfolio is $\hat w_z=\hat{\mathbf B}\hat\mu$ with $\hat{\mathbf B}=\hat\Sigma^{-1}(I-e\hat w_g^\top)$, the sample mean-variance portfolio is $\hat w^\star=\hat w_g+\frac1\gamma\hat w_z$ (10), and the shrinkage portfolio with intensity $\kappa$ is
--
--   $$\hat w^\star(\kappa)=(1-\kappa)\hat w_g+\kappa\hat w^\star\quad(11).$$
--
--   Its out-of-sample mean return and return variance are $\hat w^\star(\kappa)^\top\mu$ and $\hat w^\star(\kappa)^\top\Sigma\hat w^\star(\kappa)$. Assumption 2 says that $r_1,\dots,r_T$ are mutually independent and each has the multivariate Gaussian law $\mathcal N(\mu,\Sigma)$.
--
--   **Closed forms (p. 15).** With $T,N$ read as real numbers, $C(T,N,\psi^2)$, $a_1,a_2,a_3,a_4$ of (16)–(19), the GMV variance (14)
--
--   $$\mathbb V[U(\hat w_g)]=\frac{\sigma_g^2\psi^2}{T-N-1}+\frac{\gamma^2\sigma_g^4(N-1)(T-2)}{2(T-N-1)^2(T-N-3)},$$
--
--   and $\Delta(\kappa)=a_1\kappa^4+a_2\kappa^3+a_3\kappa^2+a_4\kappa$ (15) are defined letter for letter as printed. These are formulas only; that they equal the variance of a random variable is the content of Proposition 1.
--
--   **Formalization Note.** Vectors are `Fin N → ℝ`; returns live in `EuclideanSpace ℝ (Fin N)` because that is where Mathlib's `multivariateGaussian` lives, and `sampleData` converts them back with `WithLp.ofLp`. Assumption 2 is `iIndepFun r P` together with `HasLaw (r t) (multivariateGaussian µ Σ) P` for every $t$. Matrix inverses are Mathlib's `Matrix.inv`, which is $0$ on a singular matrix; $\hat\Sigma$ is almost surely nonsingular when $T>N$, so this convention does not affect any statement. The coefficients $a_1,a_2,a_4$ take the full argument list $(\gamma,T,N,\sigma_g^2,\psi^2)$ even when a variable does not occur, as on p. 15.
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), §3, (1)–(12), Assumptions 1–2, pp. 9–13; Proposition 1, (14)–(19) and C(T, N, ψ²), pp. 14–15

import Mathlib

namespace RiskEU.OOSUVar

open MeasureTheory ProbabilityTheory Matrix

/-- The `N`-vector of ones, `e`. -/
def ones (N : ℕ) : Fin N → ℝ := fun _ => 1

/-- A market of `N` stocks (§3.1, p. 9–10): mean excess returns `mu` (µ), covariance matrix
`Sigma` (Σ), and the investor's risk-aversion coefficient `gamma` (γ). -/
structure Market (N : ℕ) where
  mu : Fin N → ℝ
  Sigma : Matrix (Fin N) (Fin N) ℝ
  gamma : ℝ

namespace Market

variable {N : ℕ} (M : Market N)

/-- Standing assumptions: Assumption 1 (`N ≥ 2`, `T > N + 7`, p. 11), Σ positive definite (p. 9),
and γ > 0 (p. 10). -/
def Standing (T : ℕ) : Prop :=
  2 ≤ N ∧ N + 7 < T ∧ M.Sigma.PosDef ∧ 0 < M.gamma

/-- σ²_g = (eᵀΣ⁻¹e)⁻¹, eq. (6). -/
noncomputable def sigmaG2 : ℝ := (ones N ⬝ᵥ (M.Sigma⁻¹ *ᵥ ones N))⁻¹

/-- µ_g = µᵀΣ⁻¹e (eᵀΣ⁻¹e)⁻¹, eq. (5). -/
noncomputable def muG : ℝ := (M.mu ⬝ᵥ (M.Sigma⁻¹ *ᵥ ones N)) * M.sigmaG2

/-- ψ² = µᵀΣ⁻¹µ − µ_g²/σ²_g, eq. (7). -/
noncomputable def psi2 : ℝ := M.mu ⬝ᵥ (M.Sigma⁻¹ *ᵥ M.mu) - M.muG ^ 2 / M.sigmaG2

/-- The population GMV portfolio w_g = Σ⁻¹e(eᵀΣ⁻¹e)⁻¹, eq. (3). -/
noncomputable def wg : Fin N → ℝ := M.sigmaG2 • (M.Sigma⁻¹ *ᵥ ones N)

/-- The population matrix B = Σ⁻¹(I − e w_gᵀ), eq. (4). -/
noncomputable def B : Matrix (Fin N) (Fin N) ℝ := M.Sigma⁻¹ * (1 - vecMulVec (ones N) M.wg)

/-- The out-of-sample utility of a weight vector `w`, U(w) = wᵀµ − (γ/2) wᵀΣw, eqs. (1), (12),
evaluated with the population µ and Σ. -/
noncomputable def U (w : Fin N → ℝ) : ℝ := w ⬝ᵥ M.mu - M.gamma / 2 * (w ⬝ᵥ (M.Sigma *ᵥ w))

end Market

section Sample

variable {N T : ℕ}

/-- The sample mean µ̂ = (1/T) Σ_t r_t of a data matrix `x` (rows `x t` = r_t), eq. (9). -/
noncomputable def sampleMean (x : Fin T → Fin N → ℝ) : Fin N → ℝ := (T : ℝ)⁻¹ • ∑ t, x t

/-- The sample covariance Σ̂ = (1/T) Σ_t (r_t − µ̂)(r_t − µ̂)ᵀ (normalised by 1/T), eq. (9). -/
noncomputable def sampleCov (x : Fin T → Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  (T : ℝ)⁻¹ • ∑ t, vecMulVec (x t - sampleMean x) (x t - sampleMean x)

/-- The sample GMV portfolio ŵ_g = Σ̂⁻¹e(eᵀΣ̂⁻¹e)⁻¹, the sample counterpart of (3). -/
noncomputable def wHatG (x : Fin T → Fin N → ℝ) : Fin N → ℝ :=
  (ones N ⬝ᵥ ((sampleCov x)⁻¹ *ᵥ ones N))⁻¹ • ((sampleCov x)⁻¹ *ᵥ ones N)

/-- B̂ = Σ̂⁻¹(I − e ŵ_gᵀ), the sample counterpart of B in (4). -/
noncomputable def BHat (x : Fin T → Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  (sampleCov x)⁻¹ * (1 - vecMulVec (ones N) (wHatG x))

/-- The sample zero-cost portfolio ŵ_z = B̂µ̂, the sample counterpart of (4). -/
noncomputable def wHatZ (x : Fin T → Fin N → ℝ) : Fin N → ℝ := BHat x *ᵥ sampleMean x

end Sample

namespace Market

variable {N T : ℕ} (M : Market N)

/-- The sample mean-variance (SMV) portfolio ŵ* = ŵ_g + (1/γ) ŵ_z, eq. (10). -/
noncomputable def wHatMV (x : Fin T → Fin N → ℝ) : Fin N → ℝ := wHatG x + M.gamma⁻¹ • wHatZ x

/-- The shrinkage portfolio ŵ*(κ) = (1 − κ) ŵ_g + κ ŵ*, eq. (11). -/
noncomputable def wShrink (κ : ℝ) (x : Fin T → Fin N → ℝ) : Fin N → ℝ :=
  (1 - κ) • wHatG x + κ • M.wHatMV x

/-- The out-of-sample mean return ŵ*(κ)ᵀµ of the shrinkage portfolio. -/
noncomputable def oosMean (κ : ℝ) (x : Fin T → Fin N → ℝ) : ℝ := M.wShrink κ x ⬝ᵥ M.mu

/-- The out-of-sample return variance ŵ*(κ)ᵀΣŵ*(κ) of the shrinkage portfolio. -/
noncomputable def oosVar (κ : ℝ) (x : Fin T → Fin N → ℝ) : ℝ :=
  M.wShrink κ x ⬝ᵥ (M.Sigma *ᵥ M.wShrink κ x)

/-- Assumption 2 (p. 11): the returns r_1, …, r_T are mutually independent and each is
multivariate Gaussian with mean µ and covariance Σ. -/
def IsGaussianSample {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (r : Fin T → Ω → EuclideanSpace ℝ (Fin N)) : Prop :=
  iIndepFun r P ∧ ∀ t, HasLaw (r t) (multivariateGaussian (WithLp.toLp 2 M.mu) M.Sigma) P

end Market

/-- The data matrix (r_1(ω), …, r_T(ω)) of a sample, as plain vectors. -/
def sampleData {N T : ℕ} {Ω : Type*} (r : Fin T → Ω → EuclideanSpace ℝ (Fin N)) (ω : Ω) :
    Fin T → Fin N → ℝ :=
  fun t => WithLp.ofLp (r t ω)

/-! ### The closed forms of Proposition 1 (pp. 14–15), with `T`, `N` as real numbers -/

/-- C(T, N, ψ²), Proposition 1, p. 15. -/
def C (T N psi2 : ℝ) : ℝ :=
  (2 * T * psi2 + N - 1) *
      (N ^ 4 + N ^ 3 * T - 3 * N ^ 3 - 4 * N ^ 2 * T ^ 2 + 22 * N ^ 2 * T - 31 * N ^ 2 + N * T ^ 3
        - 7 * N * T ^ 2 + 13 * N * T - 5 * N + T ^ 4 - 12 * T ^ 3 + 53 * T ^ 2 - 100 * T + 70) +
    T ^ 2 * psi2 ^ 2 *
      (N ^ 3 + 2 * N ^ 2 * T - 6 * N ^ 2 - 7 * N * T ^ 2 + 40 * N * T - 53 * N + 4 * T ^ 3
        - 34 * T ^ 2 + 88 * T - 70)

set_option linter.unusedVariables false in
/-- a₁, eq. (16). -/
noncomputable def a1 (gamma T N sigmaG2 psi2 : ℝ) : ℝ :=
  1 / (2 * gamma ^ 2) * (T ^ 2 * (T - 2) * C T N psi2 /
    ((T - N) ^ 2 * (T - N - 1) ^ 2 * (T - N - 2) * (T - N - 3) ^ 2 * (T - N - 5) * (T - N - 7)))

set_option linter.unusedVariables false in
/-- a₂, eq. (17). -/
noncomputable def a2 (gamma T N sigmaG2 psi2 : ℝ) : ℝ :=
  -(2 * psi2 / gamma ^ 2) * (T ^ 2 * (T - 2) * (T + N - 3 + 2 * T * psi2) /
    ((T - N) * (T - N - 1) ^ 2 * (T - N - 3) * (T - N - 5)))

/-- a₃, eq. (18). -/
noncomputable def a3 (gamma T N sigmaG2 psi2 : ℝ) : ℝ :=
  psi2 / gamma ^ 2 * ((2 * T * (N + 1) + T ^ 2 * (T - N - 3 + 2 * (T - N) * psi2)) /
      ((T - N) * (T - N - 1) ^ 2 * (T - N - 3))) +
    sigmaG2 * (T * (T - 2) * (T + N - 3) * (T * psi2 + N - 1) /
      ((T - N) * (T - N - 1) ^ 2 * (T - N - 3) * (T - N - 5)))

set_option linter.unusedVariables false in
/-- a₄, eq. (19). -/
noncomputable def a4 (gamma T N sigmaG2 psi2 : ℝ) : ℝ :=
  -(2 * sigmaG2 * psi2) * (T * (T - 2) / ((T - N - 1) ^ 2 * (T - N - 3)))

/-- The right-hand side of (14): the OOSU variance of the sample GMV portfolio. -/
noncomputable def varGMV (gamma T N sigmaG2 psi2 : ℝ) : ℝ :=
  sigmaG2 * psi2 / (T - N - 1) +
    gamma ^ 2 * sigmaG2 ^ 2 * (N - 1) * (T - 2) / (2 * (T - N - 1) ^ 2 * (T - N - 3))

/-- Δ(κ) = a₁κ⁴ + a₂κ³ + a₃κ² + a₄κ, eq. (15). -/
noncomputable def Delta (gamma T N sigmaG2 psi2 κ : ℝ) : ℝ :=
  a1 gamma T N sigmaG2 psi2 * κ ^ 4 + a2 gamma T N sigmaG2 psi2 * κ ^ 3 +
    a3 gamma T N sigmaG2 psi2 * κ ^ 2 + a4 gamma T N sigmaG2 psi2 * κ

end RiskEU.OOSUVar


