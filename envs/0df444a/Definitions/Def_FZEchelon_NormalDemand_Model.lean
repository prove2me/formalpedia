-- Prove2me | Definitions.Def_FZEchelon_NormalDemand_Model
-- name    : FZEchelon_NormalDemand_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T11:23:57.846533+00:00
-- url     : https://prove2.me/theorems/d5302fb0-1725-413d-95e0-c151e7049ce2
-- title:
--   §1 and §4 at $\alpha=1$: normal demand, the cost $R$, the penalty $P$, $P^L$, and the functions $\tau_1,\tau_2,\tau_3,\nu^{r*},\epsilon_1,\epsilon_2,\iota,\kappa$
-- statement:
--   The model data of §4 of Federgruen and Zipkin (1984) under average costs ($\alpha=1$): mean $\mu$ and standard deviation $\sigma$ of one-period demand, cost factors $h^d$ (system-wide holding), $h^r$ (retailer holding), $p^r$ (retailer penalty), shipment lead time $l$, order lead time $L$, and the retailer's critical number $x^{r*}$.
--
--   From these the file defines:
--
--   1. $\mu^{(i)}=i\mu$ and $\sigma^{(i)}=i^{1/2}\sigma$; the law of $i$-period demand $u^{(i)}$, the normal law with mean $\mu^{(i)}$ and standard deviation $\sigma^{(i)}$; its cdf $F^{(i)}$ and density $f^{(i)}$; and $p^s=h^d+p^r$.
--   2. The retailer's cost (p. 822) at $\alpha=1$:
--   $$R(x)=-h^d(x-\mu^{(l)})+p^rE[u^{(l+1)}-x]^++(h^d+h^r)E[x-u^{(l+1)}]^+ .$$
--   3. The induced penalty cost (p. 824) at $\alpha=1$: $P(x)=0$ for $x\ge x^{r*}$ and $P(x)=R(x)-R(x^{r*})$ for $x<x^{r*}$; and $P^L(x)=E\,P[x-u^{(L)}]$, eq. (10).
--   4. The functions of p. 830:
--   $$\tau_1(x)=-\frac{x-(x^{r*}+\mu^{(L)})}{\sigma^{(L)}},\qquad \tau_2(x)=\frac{x-\mu^{(L+l+1)}}{\sigma^{(L+l+1)}},$$
--   $$\tau_3(x)=-\frac{x-(x^{r*}+\mu^{(L)})-[\sigma^{(L)}/\sigma^{(l+1)}]^2[x^{r*}-\mu^{(l+1)}]}{\sigma^{(L)}\sigma^{(L+l+1)}/\sigma^{(l+1)}},\qquad \nu^{r*}=\frac{x^{r*}-\mu^{(l+1)}}{\sigma^{(l+1)}},$$
--   $$\epsilon_1(x)=\Phi[\tau_3(x)]\phi[\tau_2(x)]/\sigma^{(L+l+1)},\qquad \epsilon_2(x)=\Phi(\nu^{r*})\phi[\tau_1(x)]/\sigma^{(L)},$$
--   the correlation $\rho=-\sigma^{(L)}/\sigma^{(L+l+1)}$, $\iota(x)=\sigma^{(L)}\Theta[\tau_1(x)]$, and
--   $$\kappa(x)=\sigma^{(l+1)}\Theta(\nu^{r*})\Phi[\tau_1(x)]-\{[\sigma^{(L+l+1)}]^2\epsilon_1(x)-[\sigma^{(L)}]^2\epsilon_2(x)\}-[x-\mu^{(L+l+1)}]\,\Phi[\tau_1(x),\tau_2(x);\rho].$$
--
--   These are the objects in the closed form (13) for $P^L$ and in the steps of its derivation.
--
--   **Formalization Note** The normal law of $u^{(i)}$ is the platform definition `InventoryControl.newsboyDemand` with mean $\mu^{(i)}$ and standard deviation $\sigma^{(i)}$, i.e. `gaussianReal (i*μ) ((√i σ)^2).toNNReal`; $F^{(i)}$ is its `ProbabilityTheory.cdf` and $f^{(i)}$ is `gaussianPDFReal` with the same parameters. Expectations are Bochner integrals; every integrand here grows at most linearly and the normal law has all moments, so none of them is a junk value. $\tau_3$ is kept in its printed form. The structure carries no hypotheses: positivity of $\sigma$ and of the costs, $L\ge1$, and the minimizing property of $x^{r*}$ are hypotheses of each theorem.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 822 (R), p. 824 (P and property (b)), p. 829 eq. (10), p. 830 (τ1, τ2, τ3, ν^{r*}, ε1, ε2, ι, κ)

import Mathlib
import Definitions.Def_InventoryControl_newsboy
import Definitions.Def_FZEchelon_NormalDemand_BivariateNormal

open MeasureTheory ProbabilityTheory Real

namespace FZEchelon.NormalDemand

/-- The data of §4 of Federgruen–Zipkin (1984) under average costs (`α = 1`): one-period demand
`u ∼ N(μ, σ²)`, holding costs `h^d` (depot echelon) and `h^r` (retailer), retail penalty cost `p^r`,
shipment lead time `l`, order lead time `L`, and the retailer's critical number `x^{r*}`. -/
structure Data where
  μ : ℝ
  σ : ℝ
  hd : ℝ
  hr : ℝ
  pr : ℝ
  l : ℕ
  L : ℕ
  xstar : ℝ

namespace Data

variable (D : Data)

/-- `μ^(i) = iμ`, the mean of `i`-period demand. -/
noncomputable def mean (i : ℕ) : ℝ := (i : ℝ) * D.μ

/-- `σ^(i) = i^{1/2} σ`, the standard deviation of `i`-period demand. -/
noncomputable def sd (i : ℕ) : ℝ := Real.sqrt (i : ℝ) * D.σ

/-- The law of `u^(i)`, the demand over `i` periods: normal with mean `μ^(i)` and standard deviation
`σ^(i)`. -/
noncomputable def law (i : ℕ) : Measure ℝ := InventoryControl.newsboyDemand (D.mean i) (D.sd i)

/-- `F^(i)`, the cdf of `u^(i)`. -/
noncomputable def F (i : ℕ) (x : ℝ) : ℝ := cdf (D.law i) x

/-- `f^(i)`, the density of `u^(i)`. -/
noncomputable def f (i : ℕ) (x : ℝ) : ℝ :=
  gaussianPDFReal (D.mean i) (Real.toNNReal (D.sd i ^ 2)) x

/-- `p^s = h^d + p^r`. -/
def ps : ℝ := D.hd + D.pr

/-- The retailer's one-period cost (p. 822) at `α = 1`:
`R(x) = -h^d(x - μ^(l)) + p^r E[u^(l+1) - x]^+ + (h^d + h^r) E[x - u^(l+1)]^+`. -/
noncomputable def R (x : ℝ) : ℝ :=
  -D.hd * (x - D.mean D.l)
    + D.pr * ∫ t, max (t - x) 0 ∂(D.law (D.l + 1))
    + (D.hd + D.hr) * ∫ t, max (x - t) 0 ∂(D.law (D.l + 1))

/-- The induced penalty cost (p. 824) at `α = 1`:
`P(x) = 0` for `x ≥ x^{r*}` and `P(x) = R(x) - R(x^{r*})` for `x < x^{r*}`. -/
noncomputable def P (x : ℝ) : ℝ := if D.xstar ≤ x then 0 else D.R x - D.R D.xstar

/-- `P^L(x) = E P[x - u^(L)]`, eq. (10). -/
noncomputable def PL (x : ℝ) : ℝ := ∫ t, D.P (x - t) ∂(D.law D.L)

/-- `τ₁(x) = -[x - (x^{r*} + μ^(L))]/σ^(L)` (p. 830). -/
noncomputable def tau1 (x : ℝ) : ℝ := -(x - (D.xstar + D.mean D.L)) / D.sd D.L

/-- `τ₂(x) = [x - μ^(L+l+1)]/σ^(L+l+1)` (p. 830). -/
noncomputable def tau2 (x : ℝ) : ℝ := (x - D.mean (D.L + D.l + 1)) / D.sd (D.L + D.l + 1)

/-- `τ₃(x) = -{x - (x^{r*} + μ^(L)) - [σ^(L)/σ^(l+1)]²[x^{r*} - μ^(l+1)]} / [σ^(L)σ^(L+l+1)/σ^(l+1)]`
(p. 830), in its printed form. -/
noncomputable def tau3 (x : ℝ) : ℝ :=
  -(x - (D.xstar + D.mean D.L) - (D.sd D.L / D.sd (D.l + 1)) ^ 2 * (D.xstar - D.mean (D.l + 1)))
    / (D.sd D.L * D.sd (D.L + D.l + 1) / D.sd (D.l + 1))

/-- `ν^{r*} = [x^{r*} - μ^(l+1)]/σ^(l+1)` (p. 830). -/
noncomputable def nustar : ℝ := (D.xstar - D.mean (D.l + 1)) / D.sd (D.l + 1)

/-- `ε₁(x) = Φ[τ₃(x)] φ[τ₂(x)] / σ^(L+l+1)` (p. 830). -/
noncomputable def eps1 (x : ℝ) : ℝ :=
  stdNormalCDF (D.tau3 x) * stdNormalPDF (D.tau2 x) / D.sd (D.L + D.l + 1)

/-- `ε₂(x) = Φ(ν^{r*}) φ[τ₁(x)] / σ^(L)` (p. 830). -/
noncomputable def eps2 (x : ℝ) : ℝ :=
  stdNormalCDF D.nustar * stdNormalPDF (D.tau1 x) / D.sd D.L

/-- The correlation `ρ = -σ^(L)/σ^(L+l+1)` used in (13) and (15). -/
noncomputable def rho : ℝ := -(D.sd D.L / D.sd (D.L + D.l + 1))

/-- `ι(x) = σ^(L) Θ[τ₁(x)]` (p. 830). -/
noncomputable def iota (x : ℝ) : ℝ := D.sd D.L * Theta (D.tau1 x)

/-- `κ(x) = σ^(l+1) Θ(ν^{r*}) Φ[τ₁(x)] - {[σ^(L+l+1)]² ε₁(x) - [σ^(L)]² ε₂(x)}
  - [x - μ^(L+l+1)] Φ[τ₁(x), τ₂(x); -σ^(L)/σ^(L+l+1)]` (p. 830). -/
noncomputable def kappa (x : ℝ) : ℝ :=
  D.sd (D.l + 1) * Theta D.nustar * stdNormalCDF (D.tau1 x)
    - (D.sd (D.L + D.l + 1) ^ 2 * D.eps1 x - D.sd D.L ^ 2 * D.eps2 x)
    - (x - D.mean (D.L + D.l + 1)) * bivNormalCDF (D.tau1 x) (D.tau2 x) D.rho

end Data

end FZEchelon.NormalDemand


