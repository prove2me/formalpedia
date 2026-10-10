-- Prove2me | Definitions.Def_TailRiskSharing_ComonoConv_Comonotone
-- name    : TailRiskSharing_ComonoConv_Comonotone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:07:56.18636+00:00
-- url     : https://prove2.me/theorems/1dab619d-6457-47a3-b4f9-92b4ed402923
-- title:
--   §6, pp. 19–20, and p. 8 — comonotonicity X//Y, comonotonic allocations (22), constrained inf-convolution ⊞ (23), tails X_p, p-generators
-- statement:
--   Objects of §6 of Liu, Mao, Wang and Wei, built on the basic setting (distribution functions, VaRs, allocations $\mathbb A_n(X)$ over a domain $\mathcal X$) and on the risk-measure vocabulary of the series.
--
--   1. Two random variables $X$ and $Y$ are **comonotonic**, written $X/\!\!/Y$, if there is $\Omega_0\in\mathcal F$ with $\mathbb P(\Omega_0)=1$ and
--   $$(X(\omega)-X(\omega'))(Y(\omega)-Y(\omega'))\ge 0\quad\text{for all }\omega,\omega'\in\Omega_0.$$
--   2. The **comonotonic allocations** of $X$ are, display (22),
--   $$\mathbb A_n^+(X)=\{(X_1,\dots,X_n)\in\mathbb A_n(X): X_i/\!\!/X,\ i=1,\dots,n\}.$$
--   3. The **constrained inf-convolution** of real-valued $\rho_1,\dots,\rho_n$ is, display (23),
--   $$\mathop{\boxplus}_{i=1}^n\rho_i(X)=\inf\Big\{\sum_{i=1}^n\rho_i(X_i):(X_1,\dots,X_n)\in\mathbb A_n^+(X)\Big\}.$$
--   4. Given a quantile uniform $U$ of $X$ (a uniform random variable on $[0,1]$ with $F^{-1}_X(U)=X$ a.s.), the **tail** of $X$ at level $p$ is $X_p=F_X^{-1}(1-p+pU)$ (p. 8).
--   5. A risk measure $\rho^*$ is a **$p$-generator** of $\rho$ (p. 20) if $\rho^*$ is law-invariant on $\mathcal X$ and $\rho(X)=\rho^*(X_p)$ for every $X\in\mathcal X$ and every quantile uniform $U$ of $X$.
--
--   Comonotonic allocations model risk sharing without sabotage, as is customary in insurance; the constrained inf-convolution is the smallest aggregate risk over such allocations.
--
--   **Formalization Note** The tail $X_p$ is written with $F^{-1}_X(q)=\mathrm{VaR}^L_{1-q}(X)$ evaluated at $q=1-p+pU(\omega)$, i.e. $\mathrm{VaR}^L_{p(1-U(\omega))}(X)$. The constrained inf-convolution is an infimum in `EReal`, never a junk real. The generator relation is required for every quantile uniform of $X$, so it does not depend on a chosen one; on an atomless space a quantile uniform exists for every $X$, so the requirement is never vacuous there. The existence of a generator (Liu and Wang 2021, Prop. 3.1) is cited by the paper and not formalized here.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 19, §6, comonotonicity, (22), (23); p. 8, tail X_p; p. 20, p-generator

import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting
import Definitions.Def_TailRiskSharing_VaRTail_Setting

namespace TailRiskSharing.ComonoConv

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- §6 p. 19: `X` and `Y` are comonotonic, `X // Y`. -/
def Comonotone (P : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ∃ Ω₀ : Set Ω, MeasurableSet Ω₀ ∧ P Ω₀ = 1 ∧
    ∀ ω ∈ Ω₀, ∀ ω' ∈ Ω₀, 0 ≤ (X ω - X ω') * (Y ω - Y ω')

/-- (22) p. 19: comonotonic allocations `A⁺_n(X)`: allocations of `X` whose every
component is comonotonic with `X`. -/
def ComonoAllocations (P : Measure Ω) (dom : Set (Ω → ℝ)) (n : ℕ) (X : Ω → ℝ) :
    Set (Fin n → Ω → ℝ) :=
  {Xs | Xs ∈ TailRiskSharing.VaRConv.Allocations dom n X ∧ ∀ i, Comonotone P (Xs i) X}

/-- (23) p. 19: the constrained (comonotonic) inf-convolution `⊞ ρᵢ`, valued in `EReal`. -/
noncomputable def comonoInfConv (P : Measure Ω) (dom : Set (Ω → ℝ)) {n : ℕ}
    (ρ : Fin n → (Ω → ℝ) → ℝ) (X : Ω → ℝ) : EReal :=
  ⨅ Xs ∈ ComonoAllocations P dom n X, ((∑ i, ρ i (Xs i) : ℝ) : EReal)

/-- p. 8: the tail `X_p = F⁻¹_X(1 − p + p U)` for a given quantile uniform `U` of `X`,
written with `F⁻¹_X(q) = VaR^L_{1-q}(X)`. -/
noncomputable def tailRV (P : Measure Ω) (p : ℝ) (X U : Ω → ℝ) : Ω → ℝ :=
  fun ω => TailRiskSharing.VaRConv.VaRL P (p * (1 - U ω)) X

/-- p. 20: `ρstar` is a `p`-generator of `ρ`: a law-invariant risk measure with
`ρ(X) = ρstar(X_p)` for every `X` in the domain and every quantile uniform `U` of `X`. -/
def IsGenerator (P : Measure Ω) (dom : Set (Ω → ℝ)) (p : ℝ) (ρ ρstar : (Ω → ℝ) → ℝ) : Prop :=
  TailRiskSharing.VaRTail.IsLawInvariant P dom ρstar ∧
    ∀ X ∈ dom, ∀ U, TailRiskSharing.VaRTail.IsQuantileUniform P X U → ρ X = ρstar (tailRV P p X U)

end TailRiskSharing.ComonoConv


