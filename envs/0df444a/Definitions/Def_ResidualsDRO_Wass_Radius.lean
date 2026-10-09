-- Prove2me | Definitions.Def_ResidualsDRO_Wass_Radius
-- name    : ResidualsDRO_Wass_Radius
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:13:16.069053+00:00
-- url     : https://prove2.me/theorems/bf069af6-9342-435d-8f2f-20947b8c1722
-- title:
--   Assumptions 1, 2, Lemma 2's bound and the enlarged radius ζ_n(α, x) of (10) (κ^(2) corrected to log(2c₁α⁻¹))
-- statement:
--   This module fixes the hypotheses and the radius used in §4 of Kannan, Bayraksan and Luedtke for Wasserstein ambiguity sets of order $p\in[1,\infty)$. The data live on a probability space $(\Omega,\mathbb P)$: the training covariates $x^i$, the errors $\varepsilon^i$ and the regression estimate $\hat f_n$ are random; $x$ is a fixed covariate realization.
--
--   1. **Assumption 1 (p. 12).** $p<a$ and $\mathbb E[\exp(\|\varepsilon\|^a)]<+\infty$ for $\varepsilon\sim P_\varepsilon$.
--   2. **Assumption 2 (p. 12) at $x$.** A function $\alpha\mapsto\kappa_{p,n}(\alpha,x)$ such that for every $\alpha\in(0,1)$, $\kappa_{p,n}(\alpha,x)>0$,
--   $$\mathbb P\big\{\|f^*(x)-\hat f_n(x)\|^p>\kappa^p_{p,n}(\alpha,x)\big\}\le\alpha,\qquad \mathbb P\Big\{\frac1n\sum_{i=1}^n\|f^*(x^i)-\hat f_n(x^i)\|^p>\kappa^p_{p,n}(\alpha,x)\Big\}\le\alpha.$$
--   3. **The bound of Lemma 2 (p. 13)** at the sample size $n$ and the covariate $x$, with constants $c_1,c_2$: for all $\kappa>0$,
--   $$\mathbb P\big\{d_{W,p}(P^*_n(x),P_{Y\mid X=x})\ge\kappa\big\}\le\begin{cases}c_1\exp(-c_2n\kappa^{\max\{d_y/p,2\}}) & \text{if }\kappa\le1,\\ c_1\exp(-c_2n\kappa^{a/p}) & \text{if }\kappa>1.\end{cases}$$
--   4. **The radius (10) (p. 15).** For $\alpha\in(0,1)$, $\zeta_n(\alpha,x)=\kappa^{(1)}_{p,n}(\alpha,x)+\kappa^{(2)}_{p,n}(\alpha)$ with $\kappa^{(1)}_{p,n}(\alpha,x)=2\kappa_{p,n}(\alpha/4,x)$ and
--   $$\kappa^{(2)}_{p,n}(\alpha)=\begin{cases}\Big(\dfrac{\log(2c_1\alpha^{-1})}{c_2n}\Big)^{\min\{p/d_y,1/2\}} & \text{if } n\ge\dfrac{\log(2c_1\alpha^{-1})}{c_2},\\[2mm] \Big(\dfrac{\log(2c_1\alpha^{-1})}{c_2n}\Big)^{p/a} & \text{if } n<\dfrac{\log(2c_1\alpha^{-1})}{c_2}.\end{cases}$$
--
--   **Correction of the page.** The paper prints $\log(c_1\alpha^{-1})$ in $\kappa^{(2)}_{p,n}(\alpha)$ and states that this term "is obtained by setting the r.h.s. of the inequality in Lemma 2 to $\alpha/2$". With $\log(c_1\alpha^{-1})$ the right-hand side of Lemma 2 at $\kappa^{(2)}_{p,n}(\alpha)$ equals $\alpha$, not $\alpha/2$; the derivation the paper states gives $\log(2c_1\alpha^{-1})$, which is used here (equivalently, (10) with $c_1$ replaced by $2c_1$).
--
--   Assumption 2 controls the regression error, the bound of Lemma 2 controls the sampling error of the true empirical distribution, and the radius adds the two allowances.
--
--   **Formalization Note** Probabilities are outer measures of the displayed sets, so no measurability of the random quantities is assumed. Assumption 2 is required only at the covariate $x$ at which the theorems are stated (the paper's "for a.e. $x$" is handled pointwise). The bound of Lemma 2 is a hypothesis on $(c_1,c_2)$, used only at the sample size $n$ and the covariate $x$; the paper quotes it from Fournier and Guillin (2015, Theorem 2), which bounds $W_p^p$ with these exponents. When $\log(2c_1\alpha^{-1})\le0$ the first branch of $\kappa^{(2)}$ applies with a nonpositive base, and Lean's real power returns a nonnegative value (the exponent lies in $(0,1/2]$ for $d_y\ge1$); every theorem using the radius assumes $d_y\ge1$.
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Math. Program. (2023), accepted manuscript, pp. 12–15, Assumption 1, Assumption 2, Lemma 2, (10)

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_ResidualsDRO_Wass_Setting

open MeasureTheory

namespace ResidualsDRO.Wass

/-- Assumption 1, p. 12: there is a constant `a > p` such that `E[exp(‖ε‖^a)] < +∞`, with
`ε ∼ P_ε`. Since `exp(‖ε‖^a)` is positive and continuous, finiteness of the expectation is
integrability. -/
def Assumption1 {Y : Type*} [NormedAddCommGroup Y] [MeasurableSpace Y]
    (Pε : Measure Y) (p a : ℝ) : Prop :=
  p < a ∧ Integrable (fun e => Real.exp (‖e‖ ^ a)) Pε

/-- Assumption 2, p. 12, at the covariate realization `x`: the function `κ : α ↦ κ_{p,n}(α, x)`
satisfies, for every risk level `α ∈ (0, 1)`, `κ_{p,n}(α, x) > 0`,
`P{‖f*(x) - f̂_n(x)‖^p > κ^p_{p,n}(α, x)} ≤ α` and
`P{(1/n) Σᵢ ‖f*(xⁱ) - f̂_n(xⁱ)‖^p > κ^p_{p,n}(α, x)} ≤ α`.
The regression estimate `fhat ω` and the training covariates `xs i ω` are random (functions of
the sample point `ω`); probabilities are the (outer) measure `P` of the displayed sets. -/
def Assumption2 {Ω X Y : Type*} [MeasurableSpace Ω] [NormedAddCommGroup Y] {n : ℕ}
    (P : Measure Ω) (fstar : X → Y) (fhat : Ω → X → Y) (xs : Fin n → Ω → X) (p : ℝ) (x : X)
    (κ : ℝ → ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 →
    0 < κ α ∧
    P {ω | κ α ^ p < ‖fstar x - fhat ω x‖ ^ p} ≤ ENNReal.ofReal α ∧
    P {ω | κ α ^ p < (n : ℝ)⁻¹ * ∑ i, ‖fstar (xs i ω) - fhat ω (xs i ω)‖ ^ p} ≤
      ENNReal.ofReal α

/-- The conclusion of Lemma 2, p. 13 (Theorem 2 of Fournier–Guillin, quoted), at the sample size
`n` and the covariate `x`, with constants `c₁, c₂`: for all `κ > 0`,
`P{d_{W,p}(P*_n(x), P_{Y|X=x}) ≥ κ} ≤ c₁ exp(-c₂ n κ^{max{d_y/p, 2}})` if `κ ≤ 1` and
`≤ c₁ exp(-c₂ n κ^{a/p})` if `κ > 1`. Here `P*_n(x)` is built from the random errors
`eps i ω`. -/
def Lemma2Bound {Ω X Y : Type*} [MeasurableSpace Ω] [NormedAddCommGroup Y] [MeasurableSpace Y]
    {n : ℕ} (P : Measure Ω) (Pε : Measure Y) (fstar : X → Y) (eps : Fin n → Ω → Y) (x : X)
    (dy : ℕ) (p a c₁ c₂ : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ →
    P {ω | ENNReal.ofReal κ ≤ WassersteinDRO.Duality.wassersteinDistance p
        (trueEmpirical fstar (fun i => eps i ω) x) (condLaw Pε fstar x)} ≤
      ENNReal.ofReal (if κ ≤ 1 then c₁ * Real.exp (-c₂ * n * κ ^ max ((dy : ℝ) / p) 2)
        else c₁ * Real.exp (-c₂ * n * κ ^ (a / p)))

/-- p. 15: `κ^{(1)}_{p,n}(α, x) := 2 κ_{p,n}(α/4, x)`, where `κ : α ↦ κ_{p,n}(α, x)`. -/
noncomputable def kappa1 (κ : ℝ → ℝ) (α : ℝ) : ℝ :=
  2 * κ (α / 4)

/-- p. 15, **corrected**: `κ^{(2)}_{p,n}(α)`, obtained (as the paper states) by setting the
right-hand side of Lemma 2 to `α/2`:
`(log(2c₁α⁻¹)/(c₂n))^{min{p/d_y, 1/2}}` if `n ≥ log(2c₁α⁻¹)/c₂`, and
`(log(2c₁α⁻¹)/(c₂n))^{p/a}` if `n < log(2c₁α⁻¹)/c₂`.
The paper prints `log(c₁α⁻¹)`; that choice sets the right-hand side of Lemma 2 to `α`, not
`α/2`, and the derivation it states gives `log(2c₁α⁻¹)`. When `log(2c₁α⁻¹) ≤ 0` the first branch
applies with a nonpositive base, and Lean's real power returns a value `≥ 0` (the exponent lies
in `(0, 1/2]` when `d_y ≥ 1`). -/
noncomputable def kappa2 (c₁ c₂ a p : ℝ) (dy n : ℕ) (α : ℝ) : ℝ :=
  if Real.log (2 * c₁ * α⁻¹) / c₂ ≤ (n : ℝ) then
    (Real.log (2 * c₁ * α⁻¹) / (c₂ * n)) ^ min (p / (dy : ℝ)) (1 / 2)
  else (Real.log (2 * c₁ * α⁻¹) / (c₂ * n)) ^ (p / a)

/-- (10), p. 15 (with the corrected `κ^{(2)}`): the enlarged radius
`ζ_n(α, x) := κ^{(1)}_{p,n}(α, x) + κ^{(2)}_{p,n}(α)`. -/
noncomputable def radius (κ : ℝ → ℝ) (c₁ c₂ a p : ℝ) (dy n : ℕ) (α : ℝ) : ℝ :=
  kappa1 κ α + kappa2 c₁ c₂ a p dy n α

end ResidualsDRO.Wass


