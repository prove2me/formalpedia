-- Prove2me | Definitions.Def_EarlyInspect_Align_Model
-- name    : EarlyInspect_Align_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:32:49.976482+00:00
-- url     : https://prove2.me/theorems/cb0b90c0-22eb-487f-bc3f-338a772d84cb
-- title:
--   §3–§4.2, pp. 58–63 — delegated stocking under scheme [M, t]: the agent's score (4), Φ, φ, ω(z) of (9), the penalty M and the inspection equation of Proposition 2, argmin sets on [I, ∞)
-- statement:
--   The single-period model of Alp and Şen's delegated stocking problem in one state of the world, under the **early-inspection scheme** $[M,t]$.
--
--   **Demand.** Cumulative demand over the period $[0,1]$ is a Wiener process with drift $\mu$ and standard deviation $\sigma>0$. Only two of its marginals are used: the period demand $D\sim N(\mu,\sigma^2)$ and the demand up to the inspection time $t\in(0,1)$, $Y_t\sim N(t\mu,\,t\sigma^2)$ (standard deviation $\sqrt t\,\sigma$).
--
--   **Standard normal.** $\Phi$ and $\varphi$ denote the distribution function and the density of $N(0,1)$.
--
--   **The agent's score.** A store manager (the agent) who raises the stock to the order-up-to level $S$ is charged one unit per unit of leftover stock and a lump-sum penalty $M$ if the shelf is empty at time $t$. His expected score, eq. (4) with $\hat c_o=1$, is
--   $$\mathrm{ETPM}_{[Mt]}(S)=\mathbb E\big[(S-D)^+\big]+M\,\mathbb P\{Y_t\ge S\}.$$
--
--   **The principal's cost** is the newsvendor cost $c_o\,\mathbb E[(S-D)^+]+c_u\,\mathbb E[(D-S)^+]$, the published `InventoryControl.newsboyCost co cu μ σ S`.
--
--   **Minimizers.** For $f:\mathbb R\to\mathbb R$ and a starting inventory $I$, $\operatorname{argmin}_{S\ge I} f$ is the set of $S\ge I$ with $f(S)\le f(S')$ for every $S'\ge I$.
--
--   **Proposition 2's quantities.** With $k=\mu/\sigma$,
--   $$M(\mu,\sigma,\hat z,\tau)=\frac{\Phi(\hat z)}{\varphi\!\left(\frac{k(1-\tau)+\hat z}{\sqrt\tau}\right)}\sqrt\tau\,\sigma,\qquad \mathrm{LHS}(k_1,k_2,\hat z,\tau)=e^{-\frac12\left[\frac{(k_2(1-\tau)+\hat z)^2-(k_1(1-\tau)+\hat z)^2}{\tau}\right]}.$$
--
--   **The function of eq. (9).** With $k=\mu/\sigma$ and $a=k(1-t)$,
--   $$\omega(z)=\Phi(z)-\frac{M}{\sqrt t\,\sigma}\,\varphi\!\left(\frac{a+z}{\sqrt t}\right).$$
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** All quantities are real. The Wiener process itself is never needed, since every statement of the mission involves only the two normal marginals above; both are the published `InventoryControl.newsboyDemand m s` (mean $m$, standard deviation $s$, variance $s^2$), so $Y_t$ is `newsboyDemand (t * μ) (Real.sqrt t * σ)`. The general weight $\hat c_o$ of eq. (4) is fixed to $1$, as in Proposition 2 and §4.1.3 ("by presetting the parameter $\hat c_o = 1$ without loss of generality"). The principal's cost uses the coefficients of the text on p. 59 (leftover stock costs $c_o$, lost demand $c_u$), not eq. (1), which prints them swapped; both $\alpha=c_u/(c_u+c_o)$ and $L_j(z)$ on p. 61 require the corrected form. The probability is of the closed half-line $\{Y_t\ge S\}$, as on the page. The integrand $(S-x)^+$ is integrable under a Gaussian law, so the Bochner integral is the true expectation. The definitions divide by $\sigma$, $\sqrt t$, $\tau$ and $\varphi(\cdot)>0$; every theorem of the mission carries $\sigma>0$ and $t,\tau\in(0,1)$, so no junk value occurs.
-- source:
--   Alp & Şen, Delegation of Stocking Decisions Under Asymmetric Demand Information, M&SOM 23(1):55–69 (2021), pp. 58–63 (PDF 5–10), §3 (eqs. (1), (4)), §4.1.2, §4.2.1 (eq. (9)), §4.2.2 (Proposition 2)

import Mathlib
import Definitions.Def_InventoryControl_newsboy

namespace EarlyInspect.Align

open MeasureTheory ProbabilityTheory InventoryControl

/-- `Φ`, the distribution function of the standard normal law (Alp & Şen, §4.1.3, p. 61). -/
noncomputable def Φ (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- `φ`, the density of the standard normal law (Alp & Şen, §4.1.3, p. 61). -/
noncomputable def φ (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

/-- The agent's expected score under scheme `[M, t]` with `ĉ_o = 1`, eq. (4), p. 60:
`E[(S − D)^+] + M · P{Y_t ≥ S}`, where the period demand is `D ~ N(μ, σ²)` and the demand up to the
inspection time `t` is `Y_t ~ N(tμ, tσ²)` (standard deviation `√t σ`). -/
noncomputable def agentCost (μ σ M t S : ℝ) : ℝ :=
  (∫ x, max (S - x) 0 ∂(newsboyDemand μ σ)) +
    M * (newsboyDemand (t * μ) (Real.sqrt t * σ)).real (Set.Ici S)

/-- The set of minimizers of `f` over the order-up-to levels `S ≥ I`. -/
def argminFrom (f : ℝ → ℝ) (I : ℝ) : Set ℝ :=
  {S | I ≤ S ∧ ∀ S', I ≤ S' → f S ≤ f S'}

/-- The penalty of Proposition 2, p. 63: `M = Φ(ẑ) / φ((k(1 − τ) + ẑ)/√τ) · √τ σ`, with `k = μ/σ`. -/
noncomputable def incentiveM (μ σ zhat τ : ℝ) : ℝ :=
  Φ zhat / φ ((μ / σ * (1 - τ) + zhat) / Real.sqrt τ) * Real.sqrt τ * σ

/-- The left-hand side of Proposition 2's inspection equation, p. 63:
`exp(−½ [((k₂(1 − τ) + ẑ)² − (k₁(1 − τ) + ẑ)²)/τ])`. -/
noncomputable def inspectionLHS (k₁ k₂ zhat τ : ℝ) : ℝ :=
  Real.exp (-(1 / 2) * (((k₂ * (1 - τ) + zhat) ^ 2 - (k₁ * (1 - τ) + zhat) ^ 2) / τ))

/-- `ω(z)` of eq. (9), p. 63: `Φ(z) − M/(√t σ) · φ((a + z)/√t)` with `k = μ/σ` and `a = k(1 − t)`. -/
noncomputable def omega (μ σ M t z : ℝ) : ℝ :=
  Φ z - M / (Real.sqrt t * σ) * φ ((μ / σ * (1 - t) + z) / Real.sqrt t)

end EarlyInspect.Align


