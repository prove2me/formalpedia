-- Prove2me | Definitions.Def_KanCombine_Optimal_Model
-- name    : KanCombine_Optimal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:08.442026+00:00
-- url     : https://prove2.me/theorems/c2d589d4-092e-446b-acea-7555704b84aa
-- title:
--   §2.1–2.3, pp. 4–10 — standing assumptions, the combining portfolio (11), the sample moments µ_g,t … σ_gz,t, the expected out-of-sample utility, k (21) and c̃* (20)
-- statement:
--   This file fixes the objects of Kan, Wang and Zhou's analysis of the combining portfolio when no risk-free asset is available. It builds on the published market model `RiskEU.OOSUVar.Setting`: a market of $N$ risky assets with mean return vector $\mu$, covariance matrix $\Sigma$ and risk-aversion coefficient $\gamma$, the GMV quantities $\sigma_g^2 = 1/(1_N'\Sigma^{-1}1_N)$ and $\mu_g = 1_N'\Sigma^{-1}\mu/(1_N'\Sigma^{-1}1_N)$, the squared slope $\psi^2 = \mu'\Sigma^{-1}\mu - \mu_g^2/\sigma_g^2$, the mean-variance utility $U(w) = w'\mu - \tfrac{\gamma}{2} w'\Sigma w$, and, from an estimation window of $h$ return vectors, the maximum-likelihood estimators $\hat\mu_t$, $\hat\Sigma_t$ (divided by $h$), the sample GMV portfolio $\hat w_{g,t} = \hat\Sigma_t^{-1}1_N/(1_N'\hat\Sigma_t^{-1}1_N)$ and the sample zero-investment portfolio $\hat w_{z,t} = \hat\Sigma_t^{-1}(\hat\mu_t - 1_N\hat\mu_{g,t})$.
--
--   On top of these it defines:
--
--   1. **Standing assumptions** for an estimation window $h$: $N \ge 2$, $h > N + 3$, $\Sigma$ positive definite and $\gamma > 0$.
--   2. The **combining portfolio** of eq. (11),
--   $$\hat w_t(\tilde c) = \hat w_{g,t} + \frac{\tilde c}{\gamma}\,\hat w_{z,t}.$$
--   3. The five **out-of-sample moments** of the two sample portfolios, evaluated at the true parameters: $\mu_{g,t} = \hat w_{g,t}'\mu$, $\mu_{z,t} = \hat w_{z,t}'\mu$, $\sigma^2_{g,t} = \hat w_{g,t}'\Sigma\hat w_{g,t}$, $\sigma^2_{z,t} = \hat w_{z,t}'\Sigma\hat w_{z,t}$ and $\sigma_{gz,t} = \hat w_{g,t}'\Sigma\hat w_{z,t}$. With them, the out-of-sample mean and variance of $\hat w_t(\tilde c)$ are $\mu_{g,t} + (\tilde c/\gamma)\mu_{z,t}$ and $\sigma^2_{g,t} + (\tilde c^2/\gamma^2)\sigma^2_{z,t} + (2\tilde c/\gamma)\sigma_{gz,t}$.
--   4. The **expected out-of-sample utility** $E[U(\hat w_t(\tilde c))]$: the utility at the true $\mu$, $\Sigma$ of the random portfolio $\hat w_t(\tilde c)$, averaged over the estimation sample.
--   5. The constants of eqs. (21) and (20),
--   $$k = \frac{(h-N)(h-N-3)}{h(h-2)}, \qquad \tilde c^* = \frac{k\psi^2}{\psi^2 + \frac{N-1}{h}}.$$
--
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note** The conditions $N \ge 2$, $\Sigma \succ 0$ and $\gamma > 0$ are implicit in the paper and made explicit here; $h > N + 3$ is the hypothesis of Lemma 1. All arithmetic in $h$ and $N$ is done in $\mathbb R$. The expectation is a Bochner integral, which is $0$ for a non-integrable integrand; the theorems of the mission therefore assert integrability alongside each expectation identity. Matrix inversion is Lean's total inverse ($0$ on a singular matrix); under a Gaussian sample with $h > N$ and $\Sigma \succ 0$, $\hat\Sigma_t$ is almost surely nonsingular, so this convention does not affect any expectation.
-- source:
--   Kan, Wang & Zhou, Optimal portfolio choice with estimation risk: No risk-free asset case, submitted manuscript (version of November 2020; SSRN 2819254, TSpace), pp. 4–10 (PDF 7–13), §2.1–2.3, eqs. (1), (7), (8), (10), (11), (15), (16), (20), (21); p. 8 (PDF 11), Lemma 1; pp. 31–32 (PDF 34–35), proof of Lemma 1

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting

namespace KanCombine.Optimal

open MeasureTheory ProbabilityTheory Matrix RiskEU.OOSUVar

/-- Standing assumptions of §2: `N ≥ 2` (added; for `N = 1` the zero-investment portfolio vanishes),
`h > N + 3` (Lemma 1, p. 8), `Σ` positive definite (implicit: `Σ⁻¹` is used throughout) and
`γ > 0` (implicit: `γ` is the risk-aversion coefficient). -/
def KanStanding {N : ℕ} (M : Market N) (h : ℕ) : Prop :=
  2 ≤ N ∧ N + 3 < h ∧ M.Sigma.PosDef ∧ 0 < M.gamma

/-- The combining portfolio `ŵ_t(c̃) = ŵ_{g,t} + (c̃/γ) ŵ_{z,t}`, eq. (11), built from a data
matrix `x` of `h` return vectors. -/
noncomputable def wComb {N h : ℕ} (M : Market N) (c : ℝ) (x : Fin h → Fin N → ℝ) : Fin N → ℝ :=
  wHatG x + (c / M.gamma) • wHatZ x

/-- `µ_{g,t} = ŵ_{g,t}′µ`, the out-of-sample mean of the sample GMV portfolio. -/
noncomputable def muGt {N h : ℕ} (M : Market N) (x : Fin h → Fin N → ℝ) : ℝ :=
  wHatG x ⬝ᵥ M.mu

/-- `µ_{z,t} = ŵ_{z,t}′µ`, the out-of-sample mean of the sample zero-investment portfolio. -/
noncomputable def muZt {N h : ℕ} (M : Market N) (x : Fin h → Fin N → ℝ) : ℝ :=
  wHatZ x ⬝ᵥ M.mu

/-- `σ²_{g,t} = ŵ_{g,t}′Σŵ_{g,t}`. -/
noncomputable def sigGt2 {N h : ℕ} (M : Market N) (x : Fin h → Fin N → ℝ) : ℝ :=
  wHatG x ⬝ᵥ (M.Sigma *ᵥ wHatG x)

/-- `σ²_{z,t} = ŵ_{z,t}′Σŵ_{z,t}`. -/
noncomputable def sigZt2 {N h : ℕ} (M : Market N) (x : Fin h → Fin N → ℝ) : ℝ :=
  wHatZ x ⬝ᵥ (M.Sigma *ᵥ wHatZ x)

/-- `σ_{gz,t} = ŵ_{g,t}′Σŵ_{z,t}`. -/
noncomputable def sigGZt {N h : ℕ} (M : Market N) (x : Fin h → Fin N → ℝ) : ℝ :=
  wHatG x ⬝ᵥ (M.Sigma *ᵥ wHatZ x)

/-- The expected out-of-sample utility `E[U(ŵ_t(c̃))]`: the utility `U` of eq. (1) at the
population `µ`, `Σ`, integrated over the estimation sample `r_1, …, r_h`. -/
noncomputable def expUtility {N h : ℕ} (M : Market N) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (r : Fin h → Ω → EuclideanSpace ℝ (Fin N)) (c : ℝ) : ℝ :=
  ∫ ω, M.U (wComb M c (sampleData r ω)) ∂P

/-- `k = (h − N)(h − N − 3)/(h(h − 2))`, eq. (21). -/
noncomputable def kCoef (N h : ℕ) : ℝ :=
  ((h : ℝ) - N) * ((h : ℝ) - N - 3) / ((h : ℝ) * ((h : ℝ) - 2))

/-- `c̃* = kψ²/(ψ² + (N − 1)/h)`, eq. (20). -/
noncomputable def cStar {N : ℕ} (M : Market N) (h : ℕ) : ℝ :=
  kCoef N h * M.psi2 / (M.psi2 + ((N : ℝ) - 1) / h)

end KanCombine.Optimal


