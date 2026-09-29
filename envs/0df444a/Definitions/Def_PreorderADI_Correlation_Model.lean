-- Prove2me | Definitions.Def_PreorderADI_Correlation_Model
-- name    : PreorderADI_Correlation_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:49:28.940009+00:00
-- url     : https://prove2.me/theorems/a5c3a534-276f-44ef-9745-f4441caf2a8c
-- title:
--   The preorder model of §3–§4: parameters, Φ, φ, the updated low-type demand, Q(x) (1), Π_L(x) (2), ξ (3), Π^p (4), μ̃(ρ) (6)
-- statement:
--   This file fixes the model of Li and Zhang's preorder strategy (§3 and §4).
--
--   A seller sells a perishable product over two periods. High-type consumers, with valuation $v_H$, arrive in the first period (the preorder season); low-type consumers, with valuation $v_L < v_H$, arrive in the second period (the regular season). A high type who waits values the product at $\delta v_H$, with $\delta \le 1$ and $\delta v_H > v_L$. The unit cost is $c$ with $0 < c < v_L$; unsold units have no salvage value and unmet demand no penalty. Write $\Delta = \delta v_H - v_L > 0$.
--
--   Demands are jointly normal. The high-type demand has mean $\mu_H > 0$ and is represented through its standardization $X$, a standard normal variable. The low-type demand has mean $\mu_L > 0$, standard deviation $\sigma_L > 0$ and $\lambda_L = \mu_L/\sigma_L$. The correlation is $\rho \in [0,1)$. Given $X = x$, the updated low-type demand $\tilde X_L(x)$ is normal with
--
--   $$
--   \tilde\mu_L(x) = \mu_L + \rho\sigma_L x, \qquad \tilde\sigma_L = \sigma_L\sqrt{1-\rho^2}.
--   $$
--
--   Let $\Phi$ and $\phi$ be the standard normal distribution function and density, and let $z_L$ be the critical-fractile quantile, $\Phi(z_L) = (v_L - c)/v_L$. The objects defined are:
--
--   1. the second-period order quantity (1): $Q(x) = \tilde\mu_L(x) + z_L\tilde\sigma_L$;
--   2. the expected second-period profit of an arbitrary order $Q$ at price $p_2 = v_L$: $\mathbb E\big[v_L\min(Q, \tilde X_L(x)) - cQ\big]$;
--   3. the second-period profit (2): $\Pi_L(x) = (v_L - c)(\mu_L + \rho\sigma_L x) - v_L\phi(z_L)\sigma_L\sqrt{1-\rho^2}$;
--   4. the consumers' availability belief (3), with the rationing parameter $\theta = 1/2$: $\xi(\rho) = \mathbb E\big[\Pr\big(\tilde X_L(X)/2 < Q(X)\big)\big]$;
--   5. the preorder profit (4): $\Pi^p(\rho) = (v_H - \Delta\xi(\rho) - c)\mu_H + \Pi_L(0)$;
--   6. the threshold (6):
--
--   $$
--   \tilde\mu(\rho) = -\frac{v_L\phi(z_L)\sigma_L}{2\Delta z_L\,\phi\big(2z_L\sqrt{1-\rho^2} + \lambda_L\big)}.
--   $$
--
--   The profit, the availability and the threshold are functions of $\rho$ with all other parameters fixed, as the paper varies them in §4.1.
--
--   **Formalization Note** The standing assumptions of §3 ($v_H > v_L$, $c < v_L$, $\delta \le 1$, $\delta v_H > v_L$) are the structure `Params.Standing`, together with four additions not written on the page: $c > 0$ (so that $(v_L-c)/v_L \in (0,1)$ and $z_L$ exists), $\sigma_L > 0$ (a non-degenerate normal law), $\mu_L > 0$ (so that $\lambda_L > 0$, as LEMMA 2 presupposes), and $\mu_H > 0$ (a positive mean demand; needed for PROPOSITION 2(ii)). The quantile $z_L = \Phi^{-1}((v_L-c)/v_L)$ is a parameter constrained by $\Phi(z_L) = (v_L-c)/v_L$ rather than a computed inverse, which avoids junk values; the equation has exactly one solution under these assumptions. $\sigma_H$ is not a parameter: after standardizing to $X$ nothing in §4 uses it. $\Phi$ is `ProbabilityTheory.cdf (gaussianReal 0 1)` and a normal law with mean $m$ and standard deviation $s$ is `gaussianReal m (s^2)`. The paper defines its rational-expectations equilibrium only through conditions (i)–(v), which already assume that every high type preorders; PROPOSITION 1 is therefore not formalized, and (4) is taken as the definition of $\Pi^p$. The integrands of $\xi$ (a probability) and of the expected newsvendor profit ($|\min(Q,y)| \le |Q| + |y|$ under a normal law) are integrable, so the Bochner integrals carry no junk value. The division in $\tilde\mu$ is well defined exactly when $z_L \ne 0$; every statement uses $\tilde\mu$ only when $z_L < 0$.
-- source:
--   Li and Zhang, Advance demand information, price discrimination, and preorder strategies, Manufacturing Service Oper. Management 15(1), 2013, pp. 60–62, §3 (model, p. 60; θ = 1/2, p. 61); §4 (1), (2), (3), p. 61; (4), p. 62; §4.1 (6), p. 62

import Mathlib

namespace PreorderADI.Correlation

open MeasureTheory ProbabilityTheory

/-- `Φ`, the standard normal distribution function (Li–Zhang 2013, §3, p. 60). -/
noncomputable def stdNormalCdf (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- `φ`, the standard normal density (Li–Zhang 2013, §3, p. 60). -/
noncomputable def stdNormalPdf (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

/-- The parameters of the preorder model of §3–§4 (p. 60): valuations `v_H`, `v_L`, unit cost `c`,
discount factor `δ`, mean high-type demand `μ_H`, mean and standard deviation `μ_L`, `σ_L` of
low-type demand, and the critical-fractile quantile `z_L` of p. 61. -/
structure Params where
  vH : ℝ
  vL : ℝ
  c : ℝ
  delta : ℝ
  muH : ℝ
  muL : ℝ
  sigmaL : ℝ
  zL : ℝ

/-- The standing assumptions of §3 (p. 60): `v_H > v_L`, `c < v_L`, `δ ≤ 1`, `δ v_H > v_L`;
the added positivity of `c`, `μ_H`, `μ_L`, `σ_L`; and `z_L = Φ⁻¹((v_L − c)/v_L)` (p. 61),
stated as `Φ(z_L) = (v_L − c)/v_L`. -/
structure Params.Standing (P : Params) : Prop where
  c_pos : 0 < P.c
  c_lt_vL : P.c < P.vL
  vL_lt_vH : P.vL < P.vH
  delta_le_one : P.delta ≤ 1
  vL_lt_delta_vH : P.vL < P.delta * P.vH
  muH_pos : 0 < P.muH
  muL_pos : 0 < P.muL
  sigmaL_pos : 0 < P.sigmaL
  zL_spec : stdNormalCdf P.zL = (P.vL - P.c) / P.vL

/-- `Δ = δ v_H − v_L` (p. 62). -/
def Params.Delta (P : Params) : ℝ := P.delta * P.vH - P.vL

/-- `λ_L = μ_L / σ_L` (p. 60). -/
noncomputable def Params.lamL (P : Params) : ℝ := P.muL / P.sigmaL

/-- `μ̃_L(x) = μ_L + ρ σ_L x`, the mean of the updated low-type demand (p. 60). -/
def lowMean (P : Params) (ρ x : ℝ) : ℝ := P.muL + ρ * P.sigmaL * x

/-- `σ̃_L = σ_L √(1 − ρ²)`, the standard deviation of the updated low-type demand (p. 60). -/
noncomputable def lowSd (P : Params) (ρ : ℝ) : ℝ := P.sigmaL * Real.sqrt (1 - ρ ^ 2)

/-- `Q(x) = μ̃_L(x) + z_L σ̃_L`, the order quantity of (1) (p. 61). -/
noncomputable def orderQty (P : Params) (ρ x : ℝ) : ℝ := lowMean P ρ x + P.zL * lowSd P ρ

/-- The law of the updated low-type demand `X̃_L(x)`: normal with mean `μ̃_L(x)` and
standard deviation `σ̃_L` (p. 60). -/
noncomputable def lowDemandLaw (P : Params) (ρ x : ℝ) : Measure ℝ :=
  gaussianReal (lowMean P ρ x) (Real.toNNReal (lowSd P ρ ^ 2))

/-- The seller's expected second-period profit when ordering `Q` at price `p_2 = v_L`, with zero
salvage value and no shortage penalty: `E[v_L min(Q, X̃_L(x)) − c Q]` (pp. 60–61). -/
noncomputable def expectedSecondProfit (P : Params) (ρ x Q : ℝ) : ℝ :=
  ∫ y, (P.vL * min Q y - P.c * Q) ∂(lowDemandLaw P ρ x)

/-- `Π_L(x) = (v_L − c)(μ_L + ρ σ_L x) − v_L φ(z_L) σ_L √(1 − ρ²)`, display (2) (p. 61). -/
noncomputable def secondProfit (P : Params) (ρ x : ℝ) : ℝ :=
  (P.vL - P.c) * (P.muL + ρ * P.sigmaL * x)
    - P.vL * stdNormalPdf P.zL * P.sigmaL * Real.sqrt (1 - ρ ^ 2)

/-- `ξ = E[Pr(X̃_L(X)/2 < Q(X))]`, the first expression of (3) (p. 61), with `X` standard
normal and the rationing belief `θ = 1/2`. -/
noncomputable def availability (P : Params) (ρ : ℝ) : ℝ :=
  ∫ x, (lowDemandLaw P ρ x).real {y | y / 2 < orderQty P ρ x} ∂(gaussianReal 0 1)

/-- `Π^p = (v_H − Δ ξ − c) μ_H + Π_L(0)`, the preorder profit (4) (p. 62), as a function of `ρ`. -/
noncomputable def preorderProfit (P : Params) (ρ : ℝ) : ℝ :=
  (P.vH - P.Delta * availability P ρ - P.c) * P.muH + secondProfit P ρ 0

/-- `μ̃(ρ) = − v_L φ(z_L) σ_L / (2 Δ z_L φ(2 z_L √(1 − ρ²) + λ_L))`, the threshold (6) (p. 62). -/
noncomputable def threshold (P : Params) (ρ : ℝ) : ℝ :=
  -(P.vL * stdNormalPdf P.zL * P.sigmaL) /
    (2 * P.Delta * P.zL * stdNormalPdf (2 * P.zL * Real.sqrt (1 - ρ ^ 2) + P.lamL))

end PreorderADI.Correlation


