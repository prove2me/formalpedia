-- Prove2me | Definitions.Def_KaufmannTS_Bernoulli_Lemma3Constants
-- name    : KaufmannTS_Bernoulli_Lemma3Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:23:49.825305+00:00
-- url     : https://prove2.me/theorems/5b098dca-8d6b-4518-9c08-6740d7e7b0ee
-- title:
--   Lemma 3 and §3.4, pp. 9, 12–13 — the constants α, λ₀, R_λ, d_λ and C_λ
-- statement:
--   Let $0<\mu_2<\mu_1<1$, let $\delta=(\mu_1-\mu_2)/2$, and put $y=\mu_2+\delta$. Lemma 3 of Kaufmann, Korda and Munos and its proof in §3.4 use the following constants, where $K(p,q)$ is the Bernoulli Kullback–Leibler divergence and $\lambda>1$:
--
--   1. $\alpha_{\mu_1,\mu_2}=(1/2)^{1-\mu_2-\delta}$;
--   2. $$\lambda_0(\mu_1,\mu_2)=1+\frac{K(\mu_2+\delta,\mu_1)}{(\mu_2+\delta)\ln\frac{1}{\mu_2+\delta}+(1-\mu_2-\delta)\ln\frac{1}{1-\mu_2-\delta}};$$
--   3. $R_\lambda=\dfrac{\mu_1(1-y)^\lambda}{y^\lambda(1-\mu_1)}$;
--   4. $d_{\lambda,\mu_1,\mu_2}=y\ln\dfrac{y^\lambda}{\mu_1}+(1-y)\ln\dfrac{(1-y)^\lambda}{1-\mu_1}$;
--   5. $$C_{\lambda,\mu_1,\mu_2}=\Big(\frac{\lambda}{e}\Big)^{\lambda}(1-\mu_2-\delta)^{-\lambda}\,\frac{R_\lambda}{R_\lambda-1}.$$
--
--   They govern how fast the posterior samples of the optimal arm escape the region below $\mu_2+\delta$ while the optimal arm is not played.
--
--   **Formalization Note** The page (p. 13) prints $C_{\lambda,\mu_1,\mu_2}=C_{\lambda_0}(1-\mu_2-\delta)^{-\lambda}R_\lambda/(1-R_\lambda)$. Since $R_\lambda>1$ in the range $1<\lambda<\lambda_0$ used, that constant is negative, which contradicts the lemma's "$C_{\lambda,\mu_1,\mu_2}>0$"; the computation on pp. 12–13 gives $C_\lambda=(\lambda/e)^\lambda$ and the factor $R_\lambda/(R_\lambda-1)$, which is what is defined here. All powers with real exponents are real powers of nonnegative bases.
-- source:
--   Kaufmann, Korda, Munos, Thompson Sampling: An Asymptotically Optimal Finite Time Analysis, arXiv:1205.4217v2, p. 9 (Lemma 3: α), p. 12 (y, R_λ, C_λ), p. 13 (d_λ, λ₀, C_{λ,µ1,µ2})

import Mathlib
import Definitions.Def_bernoulliRelativeEntropy

namespace KaufmannTS.Bernoulli

/-! Kaufmann, Korda, Munos, arXiv:1205.4217v2, Lemma 3 (p. 9) and §3.4 (pp. 11–13): the constants
of Lemma 3, as functions of the optimal mean `μ₁` and the second-best mean `μ₂`, with
`δ = (μ₁ - μ₂)/2` and `y = μ₂ + δ`. All powers with real exponents are `Real.rpow`. -/

/-- `y = μ₂ + δ = (μ₁ + μ₂)/2` (§3.4, p. 12). -/
noncomputable def lemma3Y (μ₁ μ₂ : ℝ) : ℝ := μ₂ + (μ₁ - μ₂) / 2

/-- `α_{μ₁,μ₂} = (1/2)^{1 - μ₂ - δ}` (Lemma 3, p. 9). -/
noncomputable def lemma3Alpha (μ₁ μ₂ : ℝ) : ℝ := (1 / 2 : ℝ) ^ (1 - lemma3Y μ₁ μ₂)

/-- `λ₀(μ₁, μ₂) = 1 + K(μ₂+δ, μ₁) / ((μ₂+δ) ln(1/(μ₂+δ)) + (1-μ₂-δ) ln(1/(1-μ₂-δ)))` (p. 13). -/
noncomputable def lemma3Lambda0 (μ₁ μ₂ : ℝ) : ℝ :=
  1 + BanditAlgorithm.bernoulliRelativeEntropy (lemma3Y μ₁ μ₂) μ₁ /
    (lemma3Y μ₁ μ₂ * Real.log (1 / lemma3Y μ₁ μ₂) +
      (1 - lemma3Y μ₁ μ₂) * Real.log (1 / (1 - lemma3Y μ₁ μ₂)))

/-- `R_λ(μ₁, y) = μ₁ (1-y)^λ / (y^λ (1-μ₁))` (p. 12), at `y = μ₂ + δ`. -/
noncomputable def lemma3R (lam μ₁ μ₂ : ℝ) : ℝ :=
  μ₁ * (1 - lemma3Y μ₁ μ₂) ^ lam / (lemma3Y μ₁ μ₂ ^ lam * (1 - μ₁))

/-- `d_{λ,μ₁,μ₂} = d_λ(y, μ₁) = y ln(y^λ/μ₁) + (1-y) ln((1-y)^λ/(1-μ₁))` (p. 13), at `y = μ₂ + δ`. -/
noncomputable def lemma3D (lam μ₁ μ₂ : ℝ) : ℝ :=
  lemma3Y μ₁ μ₂ * Real.log (lemma3Y μ₁ μ₂ ^ lam / μ₁) +
    (1 - lemma3Y μ₁ μ₂) * Real.log ((1 - lemma3Y μ₁ μ₂) ^ lam / (1 - μ₁))

/-- `C_{λ,μ₁,μ₂} = C_λ (1-μ₂-δ)^{-λ} R_λ / (R_λ - 1)` with `C_λ = (λ/e)^λ`, as computed on
pp. 12–13. The page prints `R_λ/(1 - R_λ)` (and `C_{λ₀}`), which is negative because `R_λ > 1`;
this is the sign-corrected constant. -/
noncomputable def lemma3C (lam μ₁ μ₂ : ℝ) : ℝ :=
  (lam / Real.exp 1) ^ lam * (1 - lemma3Y μ₁ μ₂) ^ (-lam) *
    (lemma3R lam μ₁ μ₂ / (lemma3R lam μ₁ μ₂ - 1))

end KaufmannTS.Bernoulli


