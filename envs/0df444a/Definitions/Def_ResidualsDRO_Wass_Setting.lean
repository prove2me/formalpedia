-- Prove2me | Definitions.Def_ResidualsDRO_Wass_Setting
-- name    : ResidualsDRO_Wass_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:12:21.079949+00:00
-- url     : https://prove2.me/theorems/84654eb4-acda-4100-ae2a-0c88a6dbdecd
-- title:
--   §2.1–2.2, (3), (6), (8) — projection onto 𝒴, P_{Y|X=x}, g(z; x), residuals, ε̃ⁱ_n(x), P*_n(x), P̂^ER_n(x), power mean, ER-DRO value
-- statement:
--   This module fixes the objects of the residuals-based framework of Kannan, Bayraksan and Luedtke (§2.1–§3). Throughout, $\mathcal X=\mathbb R^{d_x}$ is the covariate space, $\mathbb R^{d_y}$ the space of the dependent variables $Y$ and of the regression errors $\varepsilon$, and $\mathbb R^{d_z}$ the decision space, each with the Euclidean norm $\|\cdot\|$ and its Borel $\sigma$-algebra. The model is $Y=f^*(X)+\varepsilon$ with regression function $f^*$ and error distribution $P_\varepsilon$.
--
--   1. **Orthogonal projection.** For a nonempty closed convex set $\mathcal Y\subseteq\mathbb R^{d_y}$ (a known superset of the range of $Y$), a map $\mathrm{proj}_{\mathcal Y}$ is the orthogonal projection onto $\mathcal Y$ if for every $v$, $\mathrm{proj}_{\mathcal Y}(v)\in\mathcal Y$ and $\|v-\mathrm{proj}_{\mathcal Y}(v)\|\le\|v-y\|$ for all $y\in\mathcal Y$.
--   2. **Conditional law.** $P_{Y\mid X=x}$ is the law of $f^*(x)+\varepsilon$ with $\varepsilon\sim P_\varepsilon$.
--   3. **True objective (3).** $g(z;x)=\mathbb E[c(z,f^*(x)+\varepsilon)]$, the expectation under $P_\varepsilon$.
--   4. **Residuals and $\tilde\varepsilon$ (§2.2, (6)).** Given covariates $x^1,\dots,x^n$, errors $\varepsilon^1,\dots,\varepsilon^n$, responses $y^i=f^*(x^i)+\varepsilon^i$ and a regression estimate $\hat f_n$, the empirical residuals are $\hat\varepsilon^i_n=y^i-\hat f_n(x^i)$, and
--   $$\tilde\varepsilon^i_n(x)=(\hat f_n(x)+\hat\varepsilon^i_n)-(f^*(x)+\varepsilon^i).$$
--   5. **Empirical distributions (p. 8).**
--   $$P^*_n(x)=\frac1n\sum_{i=1}^n\delta_{f^*(x)+\varepsilon^i},\qquad \hat P^{ER}_n(x)=\frac1n\sum_{i=1}^n\delta_{\mathrm{proj}_{\mathcal Y}(\hat f_n(x)+\hat\varepsilon^i_n)}.$$
--   6. **Power mean.** $\big(\frac1n\sum_{i=1}^n v_i^p\big)^{1/p}$ for nonnegative reals $v_i$.
--   7. **ER-DRO value (8)** with the Wasserstein ambiguity set of radius $\zeta$ around $\hat P^{ER}_n(x)$:
--   $$\hat v^{DRO}_n(x)=\inf_{z\in\mathcal Z}\ \sup\Big\{\mathbb E_{Y\sim Q}[c(z,Y)]:\ Q\in\mathcal P(\mathcal Y),\ d_{W,p}(Q,\hat P^{ER}_n(x))\le\zeta\Big\}.$$
--
--   These are the objects that the finite sample certificate guarantee (Theorem 7) and its supporting lemmas relate.
--
--   **Formalization Note** The projection is a map with the nearest-point property, taken as a hypothesis on a given map (on a nonempty closed convex subset of a Euclidean space such a map exists and is unique). $P_{Y\mid X=x}$ is the pushforward of $P_\varepsilon$ under $e\mapsto f^*(x)+e$; under the paper's standing assumption that $\varepsilon$ is independent of $X$ this is the conditional distribution of $Y$ given $X=x$. The responses are not separate data: $y^i$ is written as $f^*(x^i)+\varepsilon^i$. The empirical distributions, the Wasserstein distance, the ambiguity set and the worst-case expectation are the published `WassersteinDRO.Duality` definitions; the worst-case expectation counts only distributions $Q$ in the ball under which $c(z,\cdot)$ is integrable, and $\hat v^{DRO}_n(x)$ is an extended real ($+\infty$ if $\mathcal Z=\emptyset$).
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Math. Program. (2023), accepted manuscript, pp. 5–10, Notation, §2.1 (3), §2.2 (6), §3 (8) and the Wasserstein ambiguity set

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_WassersteinDRO_Duality_ambiguitySet
import Definitions.Def_WassersteinDRO_Duality_nominalRisk
import Definitions.Def_WassersteinDRO_Duality_worstCaseRisk
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution

open MeasureTheory

namespace ResidualsDRO.Wass

/-- Notation, p. 5: `proj_𝒴`, the orthogonal projection onto a nonempty closed convex set `𝒴`,
encoded as a map `proj` with the nearest-point property: `proj v ∈ 𝒴` and
`‖v - proj v‖ ≤ ‖v - y‖` for every `y ∈ 𝒴`. On a nonempty closed convex subset of a Euclidean
space such a map exists and is unique (Mathlib: `exists_norm_eq_iInf_of_complete_convex`). -/
def IsNearestPointProj {Y : Type*} [NormedAddCommGroup Y] (𝒴 : Set Y) (proj : Y → Y) : Prop :=
  ∀ v, proj v ∈ 𝒴 ∧ ∀ y ∈ 𝒴, ‖v - proj v‖ ≤ ‖v - y‖

/-- §2.1, p. 7: `P_{Y|X=x}`, the conditional distribution of `Y = f*(X) + ε` given `X = x`,
which (ε independent of X) is the law of `f*(x) + ε` with `ε ∼ P_ε`. -/
noncomputable def condLaw {X Y : Type*} [AddCommGroup Y] [MeasurableSpace Y]
    (Pε : Measure Y) (fstar : X → Y) (x : X) : Measure Y :=
  Pε.map (fun e => fstar x + e)

/-- (3), p. 7: the true objective `g(z; x) = E[c(z, f*(x) + ε)]`, expectation under `P_ε`. -/
noncomputable def trueObjective {X Y Z : Type*} [AddCommGroup Y] [MeasurableSpace Y]
    (Pε : Measure Y) (fstar : X → Y) (c : Z → Y → ℝ) (x : X) (z : Z) : ℝ :=
  ∫ e, c z (fstar x + e) ∂Pε

/-- §2.2, p. 7: the empirical residual `ε̂ⁱ_n = yⁱ - f̂_n(xⁱ)` of the regression estimate `fhat`
on the data `(yⁱ, xⁱ)`, where `yⁱ = f*(xⁱ) + εⁱ` (model of §2.1). -/
def residual {X Y : Type*} [AddCommGroup Y] {n : ℕ} (fstar fhat : X → Y) (xs : Fin n → X)
    (eps : Fin n → Y) (i : Fin n) : Y :=
  (fstar (xs i) + eps i) - fhat (xs i)

/-- (6), p. 8: `ε̃ⁱ_n(x) := (f̂_n(x) + ε̂ⁱ_n) - (f*(x) + εⁱ)`. -/
def epsTilde {X Y : Type*} [AddCommGroup Y] {n : ℕ} (fstar fhat : X → Y) (xs : Fin n → X)
    (eps : Fin n → Y) (x : X) (i : Fin n) : Y :=
  (fhat x + residual fstar fhat xs eps i) - (fstar x + eps i)

/-- p. 8: the true empirical distribution `P*_n(x) := (1/n) Σᵢ δ_{f*(x) + εⁱ}`. -/
noncomputable def trueEmpirical {X Y : Type*} [AddCommGroup Y] [MeasurableSpace Y] {n : ℕ}
    (fstar : X → Y) (eps : Fin n → Y) (x : X) : Measure Y :=
  WassersteinDRO.Duality.empiricalDistribution (fun i => fstar x + eps i)

/-- p. 8: the estimated empirical distribution
`P̂^ER_n(x) := (1/n) Σᵢ δ_{proj_𝒴(f̂_n(x) + ε̂ⁱ_n)}`. -/
noncomputable def erEmpirical {X Y : Type*} [AddCommGroup Y] [MeasurableSpace Y] {n : ℕ}
    (proj : Y → Y) (fstar fhat : X → Y) (xs : Fin n → X) (eps : Fin n → Y) (x : X) :
    Measure Y :=
  WassersteinDRO.Duality.empiricalDistribution
    (fun i => proj (fhat x + residual fstar fhat xs eps i))

/-- pp. 13–14: the power mean `((1/n) Σᵢ vᵢ^p)^{1/p}` of nonnegative reals `v₁, …, v_n`. -/
noncomputable def powerMean {n : ℕ} (p : ℝ) (v : Fin n → ℝ) : ℝ :=
  ((n : ℝ)⁻¹ * ∑ i, v i ^ p) ^ (1 / p)

/-- (8), p. 9, with the Wasserstein ambiguity set of p. 10:
`v̂^DRO_n(x) = min_{z ∈ 𝒵} sup_{Q ∈ P(𝒴), d_{W,p}(Q, P̂^ER_n(x)) ≤ ζ} E_{Y∼Q}[c(z, Y)]`,
in `EReal` (`⊤` if `𝒵 = ∅`). The worst-case risk counts the `Q` under which `c(z, ·)` is
integrable. -/
noncomputable def erDROValue {Y Z : Type*} [NormedAddCommGroup Y] [MeasurableSpace Y]
    (𝒵 : Set Z) (c : Z → Y → ℝ) (ζ p : ℝ) (𝒴 : Set Y) (PER : Measure Y) : EReal :=
  ⨅ z ∈ 𝒵, WassersteinDRO.Duality.worstCaseRisk ζ p 𝒴 PER (c z)

end ResidualsDRO.Wass


