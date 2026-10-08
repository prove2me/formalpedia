-- Prove2me | Definitions.Def_PersistClust_Count_Setting
-- name    : PersistClust_Count_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T08:38:10.42898+00:00
-- url     : https://prove2.me/theorems/f5267991-f13f-4322-8722-72a2e60f7799
-- title:
--   §2.1, Def. 4.1, Eq. (5) — superlevel sets, densities and i.i.d. samples, shortest paths and the strong convexity radius, geodesic ε-samples, 𝒱_r, 𝒩_r
-- statement:
--   The probabilistic and geometric setting of Chazal, Guibas, Oudot and Skraba. Throughout, $\mathbb X$ is a metric space; in every theorem of the mission it is a Riemannian manifold (possibly with boundary) whose distance $d_{\mathbb X}$ is the geodesic distance.
--
--   1. **Superlevel sets.** For $f:\mathbb X\to\mathbb R$ and $\alpha\in\mathbb R$, $\mathbb F^\alpha=f^{-1}([\alpha,+\infty))=\{x : f(x)\ge\alpha\}$.
--   2. **Densities and samples.** Given a reference measure $\mu$ on $\mathbb X$, $f$ is a *probability density* if $f\ge0$, $f$ is $\mu$-integrable and $\int_{\mathbb X} f\,d\mu=1$. One sample point has law $f\cdot\mu$; $n$ i.i.d. sample points have the product law $(f\cdot\mu)^{\otimes n}$ on $\mathbb X^n$.
--   3. **Shortest paths.** A shortest path from $y$ to $y'$ is a map $\gamma:[0,d_{\mathbb X}(y,y')]\to\mathbb X$ with $\gamma(0)=y$, $\gamma(d_{\mathbb X}(y,y'))=y'$ and $d_{\mathbb X}(\gamma(s),\gamma(t))=|s-t|$ (an arc-length parametrized minimizing curve).
--   4. **Strong convexity radius.** The closed ball $B_{\mathbb X}(x,r)=\{y : d_{\mathbb X}(x,y)\le r\}$ is *strongly convex* if any two of its points are joined by exactly one shortest path in $\mathbb X$ and that path lies in the ball. $\varrho_c(x)$ is the supremum of the radii $r\ge0$ for which $B_{\mathbb X}(x,r)$ is strongly convex, and the strong convexity radius is
--   $$\varrho_c(\mathbb X)=\inf_{x\in\mathbb X}\varrho_c(x)\in[0,+\infty].$$
--   5. **Geodesic samples (Definition 4.1).** A set $L$ is a geodesic $\varepsilon$-sample of $Y$ if every $y\in Y$ satisfies $d_{\mathbb X}(y,v)\le\varepsilon$ for some $v\in L$.
--   6. **Ball measures and covering numbers (Eq. (5)).** For $A\subseteq\mathbb X$ and $r>0$,
--   $$\mathcal V_r(A)=\inf_{x\in A}\mu(B_{\mathbb X}(x,r))\in[0,+\infty],\qquad \mathcal N_r(A)\in\mathbb N\cup\{+\infty\},$$
--   where $\mathcal N_r(A)$ is the least number of closed balls of radius $r$, centered anywhere in $\mathbb X$, whose union covers $A$.
--   7. **The exponential bound.** For $a\ge0$ and $V\in[0,+\infty]$, $\mathrm{expBound}(a,V)=e^{-aV}$, with $e^{-\infty}=0$ and $0\cdot\infty=0$.
--
--   These objects state the sampling lemma (Lemma 4.3) and the probability bound of the main theorem (Theorem 4.8).
--
--   **Formalization Note** The reference measure is a parameter; the theorems instantiate it with Mathlib's $m$-dimensional Hausdorff measure $\mu_H^m$, $m=\dim\mathbb X$. Mathlib's Hausdorff measure is not normalized, so it is a constant multiple of the normalized $\mathcal H^m$ of the paper; the results of the mission are invariant under rescaling the reference measure (densities, Lipschitz constants and all thresholds rescale together). $\varrho_c$, $\mathcal V_r$ and the bound live in $[0,+\infty]$, $\mathcal N_r$ in $\mathbb N\cup\{+\infty\}$; empty infima are $+\infty$.
-- source:
--   Chazal, Guibas, Oudot, Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968 (HAL inria-00389390v1, 2009), p. 8 (§2.1), p. 9 (Eq. (2)), p. 14 (Definition 4.1), p. 17 (Eq. (5) and the r-covering number)

import Mathlib

namespace PersistClust.Count

open MeasureTheory Metric
open scoped ENNReal

noncomputable section

variable {X : Type*}

/-- The closed superlevel set `𝔽^α = f⁻¹([α, +∞))` (p. 9). -/
def superlevel (f : X → ℝ) (α : ℝ) : Set X := {x | α ≤ f x}

/-- `f` is a probability density with respect to the reference measure `μ` (§2.1, p. 8):
non-negative, `μ`-integrable, with total integral `1`. -/
def IsDensity [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ Integrable f μ ∧ ∫ x, f x ∂μ = 1

/-- The law of one sample point drawn according to the density `f`: `f · μ`. -/
def sampleLaw [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (f x))

/-- The law of `n` i.i.d. sample points drawn according to `f`: the product measure on `Fin n → X`. -/
def sampleMeasure [MeasurableSpace X] (μ : Measure X) (n : ℕ) (f : X → ℝ) : Measure (Fin n → X) :=
  Measure.pi (fun _ : Fin n => sampleLaw μ f)

/-- `γ` is a shortest path from `y` to `y'`, parametrized by arc length: an isometric embedding of
`[0, d(y, y')]` sending `0` to `y` and `d(y, y')` to `y'` (§2.1, p. 8). -/
def IsShortestPath [MetricSpace X] (y y' : X) (γ : Set.Icc (0 : ℝ) (dist y y') → X) : Prop :=
  Isometry γ ∧ γ ⟨0, le_refl 0, dist_nonneg⟩ = y ∧ γ ⟨dist y y', dist_nonneg, le_refl _⟩ = y'

/-- The closed ball `B(x, r)` is strongly convex: any two of its points are joined by exactly one
shortest path in `X`, and that path lies in the ball (§2.1, p. 8). -/
def IsStronglyConvexBall [MetricSpace X] (x : X) (r : ℝ) : Prop :=
  ∀ y ∈ closedBall x r, ∀ y' ∈ closedBall x r,
    (∃! γ : Set.Icc (0 : ℝ) (dist y y') → X, IsShortestPath y y' γ) ∧
    ∀ γ : Set.Icc (0 : ℝ) (dist y y') → X, IsShortestPath y y' γ → Set.range γ ⊆ closedBall x r

/-- `ϱ_c(x)`: the supremum of the radii `r ≥ 0` for which `B(x, r)` is strongly convex. -/
def convexityRadiusAt [MetricSpace X] (x : X) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 ≤ r) (_ : IsStronglyConvexBall x r), ENNReal.ofReal r

/-- The strong convexity radius `ϱ_c(X) = inf_x ϱ_c(x)` (§2.1, p. 8). -/
def convexityRadius (X : Type*) [MetricSpace X] : ℝ≥0∞ :=
  ⨅ x : X, convexityRadiusAt x

/-- Definition 4.1: `L` is a geodesic `ε`-sample of `Y` if every point of `Y` is within distance
`ε` of some point of `L`. -/
def IsGeodesicSample [MetricSpace X] (L Y : Set X) (ε : ℝ) : Prop :=
  ∀ y ∈ Y, ∃ v ∈ L, dist y v ≤ ε

/-- `𝒱_r(A) = inf_{x ∈ A} μ(B(x, r))`, Eq. (5) (with `inf ∅ = +∞`). -/
def minBallMeasure [MetricSpace X] [MeasurableSpace X] (μ : Measure X) (r : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ x ∈ A, μ (closedBall x r)

/-- `𝒩_r(A) ∈ ℕ ∪ {+∞}`: the least number of closed balls of radius `r`, centered anywhere in `X`,
needed to cover `A` (p. 17); `+∞` if no finite cover exists. -/
def coveringNumber [MetricSpace X] (r : ℝ) (A : Set X) : ℕ∞ :=
  ⨅ (s : Finset X) (_ : A ⊆ ⋃ x ∈ s, closedBall x r), (s.card : ℕ∞)

/-- `e^{-a V}` with the conventions `e^{-∞} = 0` and `0 · ∞ = 0`, for `a ≥ 0` and `V ∈ [0, ∞]`. -/
def expBound (a : ℝ) (V : ℝ≥0∞) : ℝ≥0∞ :=
  if ENNReal.ofReal a * V = ⊤ then 0 else ENNReal.ofReal (Real.exp (-(ENNReal.ofReal a * V).toReal))

end

end PersistClust.Count


