-- Prove2me | Definitions.Def_RiskEU_RobustShrink_Setting
-- name    : RiskEU_RobustShrink_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:28.034932+00:00
-- url     : https://prove2.me/theorems/f2ecc261-9c0b-4574-85dc-bb61c8807e33
-- title:
--   Closed-form shrinkage portfolio mean, variance, and mean-risk criterion
-- statement:
--   Let $N$ be the number of risky stocks, $T$ the number of independent historical return observations, $\gamma>0$ the investor's risk-aversion coefficient, $\sigma_g^2>0$ the population variance of the global-minimum-variance portfolio, $\psi^2\geq0$ the population return variance of the zero-cost portfolio, and $\mu_g$ the population mean return of the global-minimum-variance portfolio. The robustness weight is $\lambda\geq0$. The standing size condition is $N\geq2$; each result at a fixed sample size separately assumes $T>N+7$.
--
--   Define $C(T,N,\psi^2)$ exactly as the polynomial after (19), the coefficients $a_1,\ldots,a_4$ by (16)–(19), and
--   $$
--   V_T(\kappa)=V_T(0)+a_1\kappa^4+a_2\kappa^3+a_3\kappa^2+a_4\kappa,
--   $$
--   where $V_T(0)$ is (14). Define the OOSU mean $E_T(\kappa)$ by (IA1)–(IA2), the mean-risk criterion by
--   $$
--   R_T(\kappa)=E_T(\kappa)-\lambda\sqrt{V_T(\kappa)},
--   $$
--   and $\kappa_E(T)$ by (IA3). These formulas are the analytic interface for the paper's optimizer statements. The covariance estimator behind the coefficients uses the factor $1/T$ in (9).
--
--   **Formalization Note** The OOSU mean and variance are the closed forms from Proposition IA.1 and Proposition 1. Their identification with the moments of the random portfolio utility is established by those results and is outside this closed-form mission.
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), §3, (5)–(12), pp. 9–13; Proposition 1, (13)–(19), pp. 14–15; §5.1, (20), p. 18; Proposition IA.1, (IA1)–(IA3), p. IA1

import Mathlib

namespace RiskEU.RobustShrink

/-- The fixed market and preference parameters in the closed-form analysis. -/
structure Params where
  N : ℕ
  gamma : ℝ
  sigmaG2 : ℝ
  psi2 : ℝ
  muG : ℝ
  lam : ℝ

/-- Assumption 1's stock count, the positive risk and covariance parameters, and (20)'s weight. -/
def Params.Standing (p : Params) : Prop :=
  2 ≤ p.N ∧ 0 < p.gamma ∧ 0 < p.sigmaG2 ∧ 0 ≤ p.psi2 ∧ 0 ≤ p.lam

/-- The polynomial C(T,N,ψ²) following (19), with real arithmetic throughout. -/
def C (T N : ℕ) (psi2 : ℝ) : ℝ :=
  let t : ℝ := T
  let n : ℝ := N
  (2 * t * psi2 + n - 1) *
    (n^4 + n^3*t - 3*n^3 - 4*n^2*t^2 + 22*n^2*t - 31*n^2 + n*t^3 -
      7*n*t^2 + 13*n*t - 5*n + t^4 - 12*t^3 + 53*t^2 - 100*t + 70) +
    t^2 * psi2^2 *
    (n^3 + 2*n^2*t - 6*n^2 - 7*n*t^2 + 40*n*t - 53*n +
      4*t^3 - 34*t^2 + 88*t - 70)

/-- Coefficient a₁ of the OOSU variance polynomial, (16). -/
noncomputable def Params.a1 (p : Params) (T : ℕ) : ℝ :=
  let t : ℝ := T
  let n : ℝ := p.N
  t^2 * (t - 2) * C T p.N p.psi2 /
    (2 * p.gamma^2 * (t - n)^2 * (t - n - 1)^2 * (t - n - 2) *
      (t - n - 3)^2 * (t - n - 5) * (t - n - 7))

/-- Coefficient a₂ of the OOSU variance polynomial, (17). -/
noncomputable def Params.a2 (p : Params) (T : ℕ) : ℝ :=
  let t : ℝ := T
  let n : ℝ := p.N
  (-2 * p.psi2 * t^2 * (t - 2) * (t + n - 3 + 2*t*p.psi2)) /
    (p.gamma^2 * (t - n) * (t - n - 1)^2 * (t - n - 3) * (t - n - 5))

/-- Coefficient a₃ of the OOSU variance polynomial, (18). -/
noncomputable def Params.a3 (p : Params) (T : ℕ) : ℝ :=
  let t : ℝ := T
  let n : ℝ := p.N
  p.psi2 / p.gamma^2 *
    (2*t*(n + 1) + t^2*(t - n - 3 + 2*(t - n)*p.psi2)) /
      ((t - n)*(t - n - 1)^2*(t - n - 3)) +
  p.sigmaG2 *
    (t*(t - 2)*(t + n - 3)*(t*p.psi2 + n - 1)) /
      ((t - n)*(t - n - 1)^2*(t - n - 3)*(t - n - 5))

/-- Coefficient a₄ of the OOSU variance polynomial, (19). -/
noncomputable def Params.a4 (p : Params) (T : ℕ) : ℝ :=
  let t : ℝ := T
  let n : ℝ := p.N
  (-2*p.sigmaG2*p.psi2*t*(t - 2)) /
    ((t - n - 1)^2*(t - n - 3))

/-- OOSU variance of the sample global-minimum-variance portfolio, (14). -/
noncomputable def Params.varGMV (p : Params) (T : ℕ) : ℝ :=
  let t : ℝ := T
  let n : ℝ := p.N
  p.sigmaG2*p.psi2/(t - n - 1) +
    p.gamma^2*p.sigmaG2^2*(n - 1)*(t - 2) /
      (2*(t - n - 1)^2*(t - n - 3))

/-- The fourth-degree OOSU variance increment, (15). -/
noncomputable def Params.Delta (p : Params) (T : ℕ) (kappa : ℝ) : ℝ :=
  p.a1 T*kappa^4 + p.a2 T*kappa^3 + p.a3 T*kappa^2 + p.a4 T*kappa

/-- The closed-form OOSU variance in Proposition 1, (13)–(19). -/
noncomputable def Params.oosuVar (p : Params) (T : ℕ) (kappa : ℝ) : ℝ :=
  p.varGMV T + p.Delta T kappa

/-- OOSU mean of the sample global-minimum-variance portfolio, (IA1). -/
noncomputable def Params.meanGMV (p : Params) (T : ℕ) : ℝ :=
  let t : ℝ := T
  let n : ℝ := p.N
  p.muG - p.gamma/2 * (t - 2)/(t - n - 1)*p.sigmaG2

/-- The closed-form OOSU mean of a shrinkage portfolio, (IA2). -/
noncomputable def Params.oosuMean (p : Params) (T : ℕ) (kappa : ℝ) : ℝ :=
  let t : ℝ := T
  let n : ℝ := p.N
  p.meanGMV T + 1/p.gamma * t/(t - n - 1) *
    (kappa*p.psi2 - kappa^2*(p.psi2 + (n - 1)/t) *
      (t*(t - 2))/(2*(t - n)*(t - n - 3)))

/-- The mean-risk criterion, (20), specialized to the shrinkage portfolio. -/
noncomputable def Params.meanRisk (p : Params) (T : ℕ) (kappa : ℝ) : ℝ :=
  p.oosuMean T kappa - p.lam * Real.sqrt (p.oosuVar T kappa)

/-- The OOSU mean-maximizing intensity, (IA3). -/
noncomputable def Params.kappaE (p : Params) (T : ℕ) : ℝ :=
  let t : ℝ := T
  let n : ℝ := p.N
  ((t - n)*(t - n - 3))/(t*(t - 2)) *
    p.psi2/(p.psi2 + (n - 1)/t)

end RiskEU.RobustShrink


