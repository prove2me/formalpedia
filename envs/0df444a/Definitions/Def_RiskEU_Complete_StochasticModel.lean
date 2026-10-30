-- Prove2me | Definitions.Def_RiskEU_Complete_StochasticModel
-- name    : RiskEU_Complete_StochasticModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:02:45.427131+00:00
-- url     : https://prove2.me/theorems/77bc40bd-9461-4503-8875-9a8bdb3922dd
-- title:
--   Gaussian prefixes, actual utility objectives and portfolio consistency
-- statement:
--   Fix a market with $N$ assets, population mean $\mu\in\mathbb R^N$, covariance $\Sigma$, and risk aversion $\gamma$. The published market supplies the all-ones vector $e$, $w_g=\Sigma^{-1}e/(e^\top\Sigma^{-1}e)$, $B=\Sigma^{-1}(I-ew_g^\top)$, $\mu_g$, $\sigma_g^2$, $\psi^2$, the sample mean and covariance with divisor $T$, and the portfolio of (11). The population target is
--
--   $$w^\star=w_g+\gamma^{-1}B\mu.$$
--
--   For a real robustness weight $\lambda$, the scalar parameters are computed as $(N,\gamma,\sigma_g^2,\psi^2,\mu_g,\lambda)$ from this market. For an observation sequence $(r_t)_{t\ge0}$ on a measurable space with measure $P$, the Gaussian-sequence predicate means mutual independence and $r_t\sim\mathcal N(\mu,\Sigma)$ for every $t$. The first $T$ observations form the sample. The estimated weight vector is precisely $(1-\kappa)\hat w_{g,T}+\kappa(\hat w_{g,T}+\gamma^{-1}\hat B_T\hat\mu_T)$; both population inputs are estimated. Its utility uses the true population parameters:
--
--   $$u_{T,\kappa}=\hat w_T(\kappa)^\top\mu-\frac\gamma2\hat w_T(\kappa)^\top\Sigma\hat w_T(\kappa),\qquad E_T(\kappa)=\int u_{T,\kappa}\,dP,\qquad V_T(\kappa)=\operatorname{Var}_P(u_{T,\kappa}),\qquad R_T(\kappa)=E_T(\kappa)-\lambda\sqrt{V_T(\kappa)}.$$
--
--   A robust maximizer is a member of $[0,1]$ maximizing $R_T$ there; a variance minimizer is a member minimizing $V_T$. These predicates make no choice and assert no existence. Portfolio consistency for an intensity sequence $\kappa_T$ means
--
--   $$\forall\varepsilon>0,\quad P\{\|\hat w_T(\kappa_T)-w^\star\|_2\ge\varepsilon\}\longrightarrow0.$$
--
--   This interface connects the existing finite-sample model with the statistical conclusion of Proposition 4. It includes no moment identity, sample-covariance convergence, nonsingularity, or consistency as an assumption or model field.
--
--   **Formalization Note** Index zero denotes the paper's first observation. Real vectors are finite functions, with Euclidean norm applied after the canonical conversion. Probabilities remain extended nonnegative reals. Total inverses and integrals have Mathlib's default values outside their natural domains; the goal separately concludes almost-sure nonsingularity and finite second moments for every admissible sample size.
-- source:
--   Lassance, Martín-Utrera, and Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546, version dated August 18, 2023, §3, (2), (4), (9)–(12), pp. 10–13; (20)–(21), pp. 18–19; Proposition 4, p. 20 (PDF pp. 10–13, 18–20)

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting
import Definitions.Def_RiskEU_RobustShrink_Setting

namespace RiskEU.Complete

open MeasureTheory ProbabilityTheory Matrix
open RiskEU.OOSUVar

/-- Population optimizer (2), with the zero-cost portfolio (4). -/
noncomputable def populationWeights {N : ℕ} (M : Market N) : Fin N → ℝ :=
  M.wg + M.gamma⁻¹ • (M.B *ᵥ M.mu)

/-- Scalar formula parameters computed from the actual market, never free moment inputs. -/
noncomputable def scalarParams {N : ℕ} (M : Market N) (lam : ℝ) :
    RiskEU.RobustShrink.Params :=
  ⟨N, M.gamma, M.sigmaG2, M.psi2, M.muG, lam⟩

/-- Assumption 2 on one common observation space for every sample size. -/
def IsGaussianSequence {N : ℕ} (M : Market N) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (r : ℕ → Ω → EuclideanSpace ℝ (Fin N)) : Prop :=
  iIndepFun r P ∧
    ∀ t, HasLaw (r t) (multivariateGaussian (WithLp.toLp 2 M.mu) M.Sigma) P

/-- The first T observations; index 0 represents the paper's first observation. -/
def prefixReturns {N : ℕ} {Ω : Type*} (r : ℕ → Ω → EuclideanSpace ℝ (Fin N))
    (T : ℕ) : Fin T → Ω → EuclideanSpace ℝ (Fin N) := fun t => r t.val

/-- The actual random portfolio (9)--(11), with estimated mean AND covariance. -/
noncomputable def estimatedWeights {N : ℕ} (M : Market N) {Ω : Type*}
    (r : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (T : ℕ) (kappa : ℝ) (ω : Ω) :
    Fin N → ℝ :=
  M.wShrink kappa (sampleData (prefixReturns r T) ω)

/-- Utility (12), evaluated at the true population parameters. -/
noncomputable def samplingUtility {N : ℕ} (M : Market N) {Ω : Type*}
    (r : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (T : ℕ) (kappa : ℝ) (ω : Ω) : ℝ :=
  M.U (estimatedWeights M r T kappa ω)

/-- Actual sampling expectation; integrability is a theorem conclusion. -/
noncomputable def samplingMean {N : ℕ} (M : Market N) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (r : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (T : ℕ) (kappa : ℝ) : ℝ :=
  ∫ ω, samplingUtility M r T kappa ω ∂P

/-- Actual sampling variance, not the closed-form quartic. -/
noncomputable def samplingVariance {N : ℕ} (M : Market N) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (r : ℕ → Ω → EuclideanSpace ℝ (Fin N))
    (T : ℕ) (kappa : ℝ) : ℝ :=
  variance (samplingUtility M r T kappa) P

/-- Mean-risk robustness (20), with finite real weight lam. -/
noncomputable def samplingRobustness {N : ℕ} (M : Market N) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (r : ℕ → Ω → EuclideanSpace ℝ (Fin N))
    (lam : ℝ) (T : ℕ) (kappa : ℝ) : ℝ :=
  samplingMean M P r T kappa - lam * Real.sqrt (samplingVariance M P r T kappa)

/-- An arbitrary oracle maximizer, with its interval membership included. -/
def IsRobustMaximizer {N : ℕ} (M : Market N) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (r : ℕ → Ω → EuclideanSpace ℝ (Fin N))
    (lam : ℝ) (T : ℕ) (kappa : ℝ) : Prop :=
  kappa ∈ Set.Icc (0 : ℝ) 1 ∧
    IsMaxOn (samplingRobustness M P r lam T) (Set.Icc (0 : ℝ) 1) kappa

/-- An arbitrary variance minimizer, including membership in [0,1]. -/
def IsVarianceMinimizer {N : ℕ} (M : Market N) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (r : ℕ → Ω → EuclideanSpace ℝ (Fin N))
    (T : ℕ) (kappa : ℝ) : Prop :=
  kappa ∈ Set.Icc (0 : ℝ) 1 ∧
    IsMinOn (samplingVariance M P r T) (Set.Icc (0 : ℝ) 1) kappa

/-- Convergence in probability of the actual weight vector, in the Euclidean norm.
Probabilities remain ENNReal; no toReal default can suppress an exceptional event. -/
def PortfolioConsistent {N : ℕ} (M : Market N) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (r : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (kappa : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Filter.Tendsto
      (fun T : ℕ => P {ω | ε ≤ ‖WithLp.toLp 2
        (estimatedWeights M r T (kappa T) ω - populationWeights M)‖})
      Filter.atTop (nhds 0)

end RiskEU.Complete


