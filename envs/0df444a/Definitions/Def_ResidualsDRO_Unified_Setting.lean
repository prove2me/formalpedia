-- Prove2me | Definitions.Def_ResidualsDRO_Unified_Setting
-- name    : ResidualsDRO_Unified_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:03:15.022004+00:00
-- url     : https://prove2.me/theorems/dc61ff40-26ea-41eb-bd97-3712f1509353
-- title:
--   §2.1–2.2, §5 — the ER data model, $\hat g^{ER}_{s,n}$, $g^*_{s,n}$, $g^*_n$, $g$ and the FI-SAA process
-- statement:
--   This file fixes the objects of Kannan, Bayraksan and Luedtke's residuals-based DRO with covariate information (§2.1–2.2 and §5).
--
--   **Data model.** Responses $Y\in\mathbb R^{d_y}$ depend on covariates $X\in\mathbb R^{d_x}$ through $Y=f^*(X)+\varepsilon$, where $f^*$ is the regression function and $\varepsilon$ is the error, with law $P_\varepsilon$. A known nonempty closed convex set $\mathcal Y\subseteq\mathbb R^{d_y}$ contains the range of $Y$, and $\mathrm{proj}_{\mathcal Y}$ is the orthogonal (nearest-point) projection onto it. On a probability space $(\Omega,P)$ one observes the data $\mathcal D_n=\{(y^i,x^i)\}_{i=1}^n$ with $y^i=f^*(x^i)+\varepsilon^i$, and $\hat f_n$ is any regression estimate built from $\mathcal D_n$. The empirical residuals are $\hat\varepsilon^i_n=y^i-\hat f_n(x^i)$, and at a covariate realization $x$ the ER-SAA scenarios are $\mathrm{proj}_{\mathcal Y}(\hat f_n(x)+\hat\varepsilon^i_n)$. The combined estimation error is
--
--   $$
--   \tilde\varepsilon^i_n(x)=\bigl(\hat f_n(x)-f^*(x)\bigr)+\bigl(f^*(x^i)-\hat f_n(x^i)\bigr).
--   $$
--
--   **Unified ambiguity family (§5).** Let $\mathfrak P_n=\mathfrak P_n(x;\zeta_n(x))\subseteq\mathbb R^n$ be a set of probability vectors and $\mu_n=\mu_n(x)\ge0$ a radius. With the balls $\hat{\mathcal Y}^i_n(x;\mu_n)=\{y\in\mathcal Y:\|y-\mathrm{proj}_{\mathcal Y}(\hat f_n(x)+\hat\varepsilon^i_n)\|\le\mu_n\}$, the ER-DRO objective and its full-information counterparts are, for a decision $z\in\mathbb R^{d_z}$ and cost $c(z,y)$,
--
--   $$
--   \hat g^{ER}_{s,n}(z;x)=\sup_{p\in\mathfrak P_n}\sum_{i=1}^n p_i\sup_{y\in\hat{\mathcal Y}^i_n(x;\mu_n)}c(z,y),\qquad
--   g^*_{s,n}(z;x)=\sup_{p\in\mathfrak P_n}\sum_{i=1}^n p_i\,c(z,f^*(x)+\varepsilon^i),
--   $$
--
--   $$
--   g^*_n(z;x)=\frac1n\sum_{i=1}^n c(z,f^*(x)+\varepsilon^i)\ \text{(FI-SAA (4))},\qquad
--   g(z;x)=\mathbb E\bigl[c(z,f^*(x)+\varepsilon)\bigr]\ \text{(true objective (3))}.
--   $$
--
--   Finally, for a set $\mathcal Z$ of decisions, the **FI-SAA process** $\sqrt n\,(g^*_n(\cdot;x)-g(\cdot;x))$ is regarded as a random element of $C(\mathcal Z)$, the space of continuous real functions on $\mathcal Z$ with its Borel $\sigma$-algebra.
--
--   These are the objects in which every statement of the mission is written.
--
--   **Formalization Note** The paper's $\hat g^{ER}_{s,n}$ is, as it asserts on p. 21, the worst-case expectation of $c(z,\cdot)$ over the ambiguity set $\hat{\mathcal P}_n(x)=\{\sum_ip_i\delta_{\bar y^i}:p\in\mathfrak P_n,\ \bar y^i\in\hat{\mathcal Y}^i_n\}$; it is defined here directly by that formula and no measures are built. Sample $i\in[n]$ is Lean's `i : Fin n`, so $(x^i,\varepsilon^i)$ is `(xs (i-1), eps (i-1))`. The data $\mathcal Y$, $\mathrm{proj}$, $f^*$, the samples and $\hat f_n$ are bundled in a structure `ERData`; the projection property is the separate predicate `IsProjection`. Both suprema in $\hat g^{ER}_{s,n}$ and $g^*_{s,n}$ are real suprema; under the hypotheses of every statement ($\mathfrak P_n$ nonempty, $\mu_n\ge0$, $c(z,\cdot)$ Lipschitz on $\mathcal Y$) their index sets are nonempty and the values bounded, so Lean's convention $\sup\emptyset=0$ never applies. $g$ is a Bochner integral; integrability is assumed wherever $g$ appears. The FI-SAA process is `0` when $\sqrt n(g^*_n-g)$ is not continuous on $\mathcal Z$, a case Assumption 14 excludes.
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Math. Program. (2023), accepted manuscript, pp. 5–9 and 20–23, Notation, §2.1–2.2 (3)–(6), problem (8), §5 (definitions of the ambiguity family, ĝ^ER_{s,n} and g*_{s,n}), Assumption 14

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace ResidualsDRO.Unified

/-! Kannan, Bayraksan & Luedtke, *Residuals-based distributionally robust optimization with
covariate information*, Math. Program. (2023), accepted manuscript: the data model of §2.1–2.2
(pp. 6–8), problem (8) (p. 9) and the unified ambiguity family of §5 (p. 20).

Conventions. `X = ℝ^{d_x}`, `Y = ℝ^{d_y}` (the space of `Y` and of the errors `ε`) and
`ℝ^{d_z}` (the decisions) are Euclidean spaces with the `ℓ₂` norm. The paper's sample index
`i ∈ [n] = {1, …, n}` is `i : Fin n`, i.e. the sample `(xⁱ, εⁱ)` is `(xs i, eps i)` with
`i = 0, …, n - 1`. -/

/-- `proj` is the orthogonal (nearest-point) projection onto the set `𝒴`: it maps into `𝒴` and
`proj v` is a point of `𝒴` closest to `v` (Notation, p. 5). -/
def IsProjection {dy : ℕ} (𝒴 : Set (EuclideanSpace ℝ (Fin dy)))
    (proj : EuclideanSpace ℝ (Fin dy) → EuclideanSpace ℝ (Fin dy)) : Prop :=
  ∀ v, proj v ∈ 𝒴 ∧ ∀ w ∈ 𝒴, ‖v - proj v‖ ≤ ‖v - w‖

/-- The data of the residuals-based setup (§2.1–2.2, pp. 6–8) on a sample space `Ω`:
* `𝒴 ⊆ ℝ^{d_y}`, the known superset of the range of `Y`, with a projection `proj` onto it;
* `fstar`, the regression function `f*`;
* `xs i`, `eps i`, the covariate `x^{i+1}` and the error `ε^{i+1} = y^{i+1} - f*(x^{i+1})` of
  the `(i+1)`-st observation, as random variables on `Ω`; the response is
  `y^{i+1} = f*(x^{i+1}) + ε^{i+1}`;
* `fhat n`, the regression estimate `f̂_n` built from the first `n` observations `𝒟_n`
  (any data-dependent map `ℝ^{d_x} → ℝ^{d_y}`). -/
structure ERData (dx dy : ℕ) (Ω : Type*) where
  𝒴 : Set (EuclideanSpace ℝ (Fin dy))
  proj : EuclideanSpace ℝ (Fin dy) → EuclideanSpace ℝ (Fin dy)
  fstar : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin dy)
  xs : ℕ → Ω → EuclideanSpace ℝ (Fin dx)
  eps : ℕ → Ω → EuclideanSpace ℝ (Fin dy)
  fhat : ℕ → Ω → EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin dy)

variable {dx dy dz : ℕ} {Ω : Type*}

/-- The empirical residual `ε̂ⁱ_n = yⁱ - f̂_n(xⁱ) = f*(xⁱ) + εⁱ - f̂_n(xⁱ)` (p. 7). -/
def residual (D : ERData dx dy Ω) (n : ℕ) (ω : Ω) (i : Fin n) : EuclideanSpace ℝ (Fin dy) :=
  D.fstar (D.xs i ω) + D.eps i ω - D.fhat n ω (D.xs i ω)

/-- The ER-SAA scenario `proj_𝒴(f̂_n(x) + ε̂ⁱ_n)` (problem (5), p. 7). -/
def scenario (D : ERData dx dy Ω) (x : EuclideanSpace ℝ (Fin dx)) (n : ℕ) (ω : Ω) (i : Fin n) :
    EuclideanSpace ℝ (Fin dy) :=
  D.proj (D.fhat n ω x + residual D n ω i)

/-- `ε̃ⁱ_n(x) = (f̂_n(x) - f*(x)) + (f*(xⁱ) - f̂_n(xⁱ))` (below (6), p. 8). -/
def epsTilde (D : ERData dx dy Ω) (x : EuclideanSpace ℝ (Fin dx)) (n : ℕ) (ω : Ω) (i : Fin n) :
    EuclideanSpace ℝ (Fin dy) :=
  (D.fhat n ω x - D.fstar x) + (D.fstar (D.xs i ω) - D.fhat n ω (D.xs i ω))

/-- The sample-robust ball `Ŷⁱ_n(x; μ) = {y ∈ 𝒴 : ‖y - proj_𝒴(f̂_n(x) + ε̂ⁱ_n)‖ ≤ μ}` (§5, p. 20). -/
def scenarioBall (D : ERData dx dy Ω) (x : EuclideanSpace ℝ (Fin dx)) (μ : ℝ) (n : ℕ) (ω : Ω)
    (i : Fin n) : Set (EuclideanSpace ℝ (Fin dy)) :=
  {y | y ∈ D.𝒴 ∧ ‖y - scenario D x n ω i‖ ≤ μ}

/-- The ER-DRO objective of §5 (p. 20) for the unified ambiguity family:
`ĝ^ER_{s,n}(z; x) = sup_{p ∈ 𝔓_n} ∑ᵢ pᵢ sup_{y ∈ Ŷⁱ_n(x; μ_n)} c(z, y)`.
Here `𝔓 n ⊆ ℝⁿ` is the set `𝔓_n(x; ζ_n(x))` of probability vectors and `μ n` the radius
`μ_n(x)`. Both suprema are real suprema; they are finite and attained-or-approached on the
nonempty bounded index sets supplied by the hypotheses of every statement that uses this
objective. -/
noncomputable def ghatER (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (D : ERData dx dy Ω) (x : EuclideanSpace ℝ (Fin dx)) (𝔓 : (n : ℕ) → Set (Fin n → ℝ))
    (μ : ℕ → ℝ) (n : ℕ) (ω : Ω) (z : EuclideanSpace ℝ (Fin dz)) : ℝ :=
  ⨆ p : 𝔓 n, ∑ i, (p : Fin n → ℝ) i * ⨆ y : scenarioBall D x (μ n) n ω i, c z y

/-- `g*_{s,n}(z; x) = sup_{p ∈ 𝔓_n} ∑ᵢ pᵢ c(z, f*(x) + εⁱ)` (§5, p. 20). -/
noncomputable def gstarS (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (D : ERData dx dy Ω) (x : EuclideanSpace ℝ (Fin dx)) (𝔓 : (n : ℕ) → Set (Fin n → ℝ))
    (n : ℕ) (ω : Ω) (z : EuclideanSpace ℝ (Fin dz)) : ℝ :=
  ⨆ p : 𝔓 n, ∑ i, (p : Fin n → ℝ) i * c z (D.fstar x + D.eps i ω)

/-- The full-information SAA objective (4), p. 7: `g*_n(z; x) = (1/n) ∑ᵢ c(z, f*(x) + εⁱ)`. -/
noncomputable def gstarN (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (D : ERData dx dy Ω) (x : EuclideanSpace ℝ (Fin dx)) (n : ℕ) (ω : Ω)
    (z : EuclideanSpace ℝ (Fin dz)) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i : Fin n, c z (D.fstar x + D.eps i ω)

/-- The true objective (3), p. 7: `g(z; x) = E[c(z, f*(x) + ε)]`, the expectation under the law
`Pε` of the error `ε` (a Bochner integral; every statement assumes the integrability). -/
noncomputable def gTrue (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (D : ERData dx dy Ω) (x : EuclideanSpace ℝ (Fin dx)) (Pε : Measure (EuclideanSpace ℝ (Fin dy)))
    (z : EuclideanSpace ℝ (Fin dz)) : ℝ :=
  ∫ e, c z (D.fstar x + e) ∂Pε

/-- The space `C(S)` of real continuous functions on `S` carries its Borel σ-algebra
(for compact `S` its topology is that of the supremum norm). -/
scoped instance instMeasurableSpaceContinuousMap {α : Type*} [TopologicalSpace α] :
    MeasurableSpace C(α, ℝ) := borel _

scoped instance instBorelSpaceContinuousMap {α : Type*} [TopologicalSpace α] :
    BorelSpace C(α, ℝ) := ⟨rfl⟩

open Classical in
/-- The FI-SAA process `√n (g*_n(·; x) - g(·; x))` of Assumption 14 (p. 23), as an element of
`C(𝒵)`. When this function is not continuous on `𝒵` the value is `0`; Assumption 14 requires
`g*_n(·; x)` and `g(·; x)` to be continuous on `𝒵`, which excludes that case. -/
noncomputable def fcltProcess (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (D : ERData dx dy Ω) (x : EuclideanSpace ℝ (Fin dx)) (Pε : Measure (EuclideanSpace ℝ (Fin dy)))
    (𝒵 : Set (EuclideanSpace ℝ (Fin dz))) (n : ℕ) (ω : Ω) : C(𝒵, ℝ) :=
  if h : Continuous (fun z : 𝒵 => Real.sqrt n * (gstarN c D x n ω z - gTrue c D x Pε z)) then
    ⟨_, h⟩
  else 0

end ResidualsDRO.Unified


