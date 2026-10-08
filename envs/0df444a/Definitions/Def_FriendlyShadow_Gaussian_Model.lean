-- Prove2me | Definitions.Def_FriendlyShadow_Gaussian_Model
-- name    : FriendlyShadow_Gaussian_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T19:53:14.851025+00:00
-- url     : https://prove2.me/theorems/3bcd676a-cb76-4072-b8e8-e4e7391da6c1
-- title:
--   §3, Defs 15–18, 23, 28, 43 — the shadow polygon conv(a₁,…,aₙ) ∩ W, its edges and perimeter, the distribution parameters, and the Laplace–Gaussian density
-- statement:
--   This file fixes the objects of §3 of Dadush and Huiberts' smoothed analysis of the shadow vertex simplex method. Throughout, $\mathbb R^d$ is Euclidean space with inner product $x^\mathsf{T}y$ and norm $\|\cdot\|$, $a_1,\dots,a_n\in\mathbb R^d$ are the constraint vectors, and $W\subseteq\mathbb R^d$ is a linear subspace (in every statement, a fixed plane).
--
--   1. **Polygon.** $Q=\operatorname{conv}(a_1,\dots,a_n)$ and the shadow polygon is $Q\cap W$.
--   2. **Edges.** An edge of a set $K$ is a segment $[u,v]$, $u\ne v$, that is an extreme subset of $K$ (the published relation `Hirsch.Adj`). The set of edges $\operatorname{edges}(K)$ consists of these segments, each counted once, and $|\operatorname{edges}(K)|$ is their number.
--   3. **Perimeter and length.** $\operatorname{perimeter}(K)$ is the sum of the lengths of the edges of $K$, and for $I\subseteq[n]$, $\operatorname{length}(\operatorname{conv}(a_i:i\in I)\cap W)$ is the diameter of that set.
--   4. **The event $E_I$** (Definition 23): $\operatorname{conv}(a_i : i\in I)\cap W$ is an edge of $Q\cap W$.
--   5. **The event $D$** (Definition 28) for $I$ and a radius $R$: with $l=\operatorname{aff}(a_i:i\in I)\cap W=p+\omega\mathbb R$,
--   $$\|\pi_{\omega^\perp}(a_i)-\pi_{\omega^\perp}(a_j)\|\le 2+2R\qquad\text{for all } i,j\in I.$$
--   6. **Densities.** A probability density $\mu$ on $\mathbb R^d$ is nonnegative, integrable, of total mass $1$; it has mean $y$ if $\int x\,\mu(x)\,dx=y$. Independent rows with densities $\mu_1,\dots,\mu_n$ have the product law.
--   7. **$L$-log-Lipschitz** (Definition 15): $\mu>0$ and $\mu(x)\le e^{L\|x-y\|}\mu(y)$ for all $x,y$.
--   8. **Line variance at least $\tau^2$** (Definition 16): for every line $v+w\mathbb R$, $\|w\|=1$, the restriction $\gamma\mapsto\mu(v+\gamma w)$, normalised to a probability density on $\mathbb R$, has variance at least $\tau^2$.
--   9. **$n$-th deviation at most $r$** (Definition 17): for every unit vector $\theta$, with $y$ the mean,
--   $$\int_r^\infty \Pr_{X\sim\mu}\big[|(X-y)^\mathsf{T}\theta|\ge t\big]\,dt\le \frac rn .$$
--   10. **Cutoff radius $R(p)$ at most $R$** (Definition 18): $\Pr_{X\sim\mu}[\|X-y\|\ge R]\le p$. The level of interest is $p=1/(d\binom nd)$, giving $R_{n,d}$.
--   11. **Laplace–Gaussian distribution** (Definition 43): $LG_d(\bar a,\sigma,r)$ has density proportional to
--   $$f_{(\bar a,\sigma,r)}(x)=\begin{cases}e^{-\|x-\bar a\|^2/(2\sigma^2)} & \|x-\bar a\|\le r\sigma,\\ e^{-\|x-\bar a\|r/\sigma+r^2/2} & \|x-\bar a\|\ge r\sigma.\end{cases}$$
--
--   These are the objects of Theorems 13 and 22 and of Lemmas 19–46 of the mission.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` and $[n]$ is `Fin n`. The paper defines $r_n$ and $R(p)$ as "the smallest number such that…"; the predicates `NthDeviationLE` and `CutoffRadiusLE` state "the paper's number is at most $r$ (resp. $R$)", which is equivalent because the left-hand sides are monotone and (for a density) continuous; every theorem of the paper uses these parameters only as upper bounds. The line variance is a lower-bound predicate stated multiplied by the squared slice mass; lines along which the slice has infinite mass are skipped, and a slice with infinite second moment satisfies the bound (its variance is infinite). Positivity is part of log-Lipschitzness, since the paper's logarithmic form needs it. The tail integral of Definition 17 is a lower Lebesgue integral of probabilities in $[0,\infty]$, so it never takes a junk value. The perimeter is the sum of edge lengths; when $Q\cap W$ is a single segment it is that segment's length, which is how the proof of Lemma 25 counts it. Lengths are extended diameters of compact sets, hence finite. The normalised Laplace–Gaussian density divides by the integral of $f$, which is finite and positive for $\sigma>0$, $r>0$ (every statement assumes this).
-- source:
--   Dadush & Huiberts, arXiv:1711.05667v4, §3.1.2 setting and Defs 23, 27, 28 (pp. 22, 24), Defs 15–18 (p. 20), Def 43 (p. 33), Lemma 25 proof (p. 23)

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_SmoothedSimplex_Shadow_gaussian

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace FriendlyShadow.Gaussian

/-! ### The shadow polygon `conv(a₁, …, aₙ) ∩ W`, its edges and its perimeter -/

/-- The **shadow polygon** `Q ∩ W`, where `Q = conv(a₁, …, aₙ)` is the convex hull of the
constraint vectors `a i ∈ ℝᵈ` and `W` is a (two-dimensional) linear subspace of `ℝᵈ`
(Dadush–Huiberts, arXiv:1711.05667v4, §3.1.2, p. 22). -/
def polygon {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  convexHull ℝ (Set.range a) ∩ (W : Set (EuclideanSpace ℝ (Fin d)))

/-- The set of **edges** of a set `K ⊆ ℝᵈ`: the segments `[u, v]` with `u ≠ v` that are extreme
subsets of `K` (`Hirsch.Adj K u v`). An edge is recorded as a set, so `[u, v]` and `[v, u]` are
the same edge. -/
def edges {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) :
    Set (Set (EuclideanSpace ℝ (Fin d))) :=
  {F | ∃ u v, Hirsch.Adj K u v ∧ F = segment ℝ u v}

/-- `|edges(K)|`, the number of edges of `K`. For the compact polygon `Q ∩ W` the edge set is
finite. -/
noncomputable def edgeCount {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) : ℕ :=
  (edges K).ncard

/-- The **perimeter** of `K`: the sum of the lengths of its edges, a length being the
(extended) diameter of the segment. For the polygon `Q ∩ W` (a convex polygon inside the plane
`W`) this is its boundary length inside `W`; when `Q ∩ W` is a single segment it is the length
of that segment, which is how the paper's proof of Lemma 25 counts it
(`E[perimeter] = Σ_I E[length(conv(aᵢ : i ∈ I) ∩ W) | E_I] Pr[E_I]`, p. 23). -/
noncomputable def perimeter {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ∑' F : edges K, Metric.ediam (F : Set (EuclideanSpace ℝ (Fin d)))

/-- `length(conv(aᵢ : i ∈ I) ∩ W)`: the (extended) diameter of the intersection of the
simplex spanned by the vectors indexed by `I` with `W`. This set is compact, so the value is
finite; on the event `E_I` it is the length of the edge `conv(aᵢ : i ∈ I) ∩ W`. -/
noncomputable def edgeLen {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (I : Finset (Fin n)) : ℝ≥0∞ :=
  Metric.ediam (convexHull ℝ (a '' (I : Set (Fin n))) ∩ (W : Set (EuclideanSpace ℝ (Fin d))))

/-- The event `E_I` of Definition 23 (p. 22): `conv(aᵢ : i ∈ I) ∩ W` forms an edge of `Q ∩ W`. -/
def edgeEvent {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (I : Finset (Fin n)) : Prop :=
  ∃ u v, Hirsch.Adj (polygon W a) u v ∧
    convexHull ℝ (a '' (I : Set (Fin n))) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) = segment ℝ u v

/-- The direction of the line `l = H ∩ W` of Definition 27 (p. 24), where
`H = aff(aᵢ : i ∈ I)`: the intersection of the direction of `H` with `W`. Under the paper's
non-degeneracy conditions (which hold almost surely) and on `E_I` it is the line `ω · ℝ`. -/
noncomputable def lineDir {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (I : Finset (Fin n)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  (affineSpan ℝ (a '' (I : Set (Fin n)))).direction ⊓ W

/-- The bounded diameter event `D` of Definition 28 (p. 24), for the index set `I` and the
cutoff radius bound `R`: `‖π_{ω⊥}(aᵢ) − π_{ω⊥}(aⱼ)‖ ≤ 2 + 2R` for all `i, j ∈ I`, where
`π_{ω⊥}` is the orthogonal projection onto the orthogonal complement of `lineDir W a I`. -/
def boundedDiamEvent {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (I : Finset (Fin n)) (R : ℝ) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, ‖(lineDir W a I)ᗮ.starProjection (a i - a j)‖ ≤ 2 + 2 * R

/-! ### Densities and the distribution parameters of Definitions 15–18 (p. 20) -/

/-- `μ` is a probability density on `ℝᵈ`: nonnegative, Lebesgue integrable, total mass `1`. -/
def IsDensity {d : ℕ} (μ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ Integrable μ ∧ ∫ x, μ x = 1

/-- The measure with density `μ` with respect to Lebesgue measure on `ℝᵈ`. -/
noncomputable def densityMeasure {d : ℕ} (μ : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  volume.withDensity (fun x => ENNReal.ofReal (μ x))

/-- The joint law of independent rows `a₁, …, aₙ`, row `i` having density `μ i`. -/
noncomputable def rowLaw {d n : ℕ} (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) :
    Measure (Fin n → EuclideanSpace ℝ (Fin d)) :=
  Measure.pi (fun i => densityMeasure (μ i))

/-- The density `μ` has expectation `y`: `∫ x μ(x) dx` exists and equals `y`. -/
def HasMean {d : ℕ} (μ : EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d)) : Prop :=
  Integrable (fun x => μ x • x) ∧ ∫ x, μ x • x = y

/-- Definition 15 (p. 20): `μ` is `L`-log-Lipschitz, in the page's equivalent form
`μ(x)/μ(y) ≤ exp(L‖x − y‖)` for all `x, y`. Positivity is part of the definition (the
logarithm of the page's first form is only meaningful for a positive density). -/
def LogLipschitz {d : ℕ} (μ : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) : Prop :=
  (∀ x, 0 < μ x) ∧ ∀ x y, μ x ≤ Real.exp (L * ‖x - y‖) * μ y

/-- Definition 16 (p. 20), as a lower bound: the line variance of `μ` is at least `τ²`.
For every line `v + ℝ w` (`‖w‖ = 1`) the restriction of `μ` to the line,
`γ ↦ μ(v + γ w)`, normalised to a probability density on `ℝ`, has variance at least `τ²`.
With `M_k = ∫ γ^k μ(v + γ w) dγ` the variance is `M₂/M₀ − (M₁/M₀)²`; the condition is stated
multiplied by `M₀² > 0`. Lines along which the restriction has infinite mass are skipped (the
conditional law is undefined there), and a restriction with infinite second moment has infinite
variance, so it satisfies the bound automatically. -/
def LineVarianceGE {d : ℕ} (μ : EuclideanSpace ℝ (Fin d) → ℝ) (τ : ℝ) : Prop :=
  ∀ v w : EuclideanSpace ℝ (Fin d), ‖w‖ = 1 →
    Integrable (fun γ : ℝ => μ (v + γ • w)) →
    Integrable (fun γ : ℝ => γ ^ 2 * μ (v + γ • w)) →
    0 < ∫ γ : ℝ, μ (v + γ • w) →
    τ ^ 2 * (∫ γ : ℝ, μ (v + γ • w)) ^ 2 ≤
      (∫ γ : ℝ, γ ^ 2 * μ (v + γ • w)) * (∫ γ : ℝ, μ (v + γ • w)) -
        (∫ γ : ℝ, γ * μ (v + γ • w)) ^ 2

/-- Definition 17 (p. 20), as an upper bound: the `n`-th deviation of `μ` (whose mean is `y`)
is at most `r`, i.e. for every unit vector `θ`,
`∫_r^∞ Pr_{X∼μ}[|(X − y)ᵀθ| ≥ t] dt ≤ r/n`.
Since the left side is nonincreasing in `r` and the right side increasing, this holds exactly
when the page's `rₙ` (the smallest such number) is `≤ r`. -/
def NthDeviationLE {d : ℕ} (μ : EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d))
    (n : ℕ) (r : ℝ) : Prop :=
  ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ = 1 →
    ∫⁻ t in Set.Ioi r, densityMeasure μ {x | t ≤ |⟪x - y, θ⟫|} ≤ ENNReal.ofReal (r / n)

/-- Definition 18 (p. 20), as an upper bound: the cutoff radius `R(p)` of `μ` (mean `y`) is at
most `R`, i.e. `Pr_{x∼μ}[‖x − y‖ ≥ R] ≤ p`. Because `μ` has a density, the tail probability is
continuous in `R`, so this holds exactly when the page's `R(p)` is `≤ R`. -/
def CutoffRadiusLE {d : ℕ} (μ : EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d))
    (p R : ℝ) : Prop :=
  densityMeasure μ {x | R ≤ ‖x - y‖} ≤ ENNReal.ofReal p

/-- The probability level `1/(d·C(n, d))` of the cutoff radius of interest `R_{n,d}`. -/
noncomputable def cutoffLevel (n d : ℕ) : ℝ :=
  1 / ((d : ℝ) * (n.choose d : ℝ))

/-! ### The Laplace–Gaussian distribution of Definition 43 (p. 33) -/

/-- The unnormalised Laplace–Gaussian density `f_(ā,σ,r)`:
`exp(−‖x − ā‖²/(2σ²))` if `‖x − ā‖ ≤ rσ`, and `exp(−‖x − ā‖ r/σ + r²/2)` otherwise.
Both branches equal `exp(−r²/2)` at `‖x − ā‖ = rσ`. -/
noncomputable def lgDensity {d : ℕ} (abar : EuclideanSpace ℝ (Fin d)) (σ r : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  if ‖x - abar‖ ≤ r * σ then Real.exp (-(‖x - abar‖ ^ 2) / (2 * σ ^ 2))
  else Real.exp (-(‖x - abar‖ * r / σ) + r ^ 2 / 2)

/-- The normalised Laplace–Gaussian density: `f_(ā,σ,r)` divided by its integral. For `σ > 0`
and `r > 0` the integral is finite and positive, so this is a probability density. -/
noncomputable def lgPdf {d : ℕ} (abar : EuclideanSpace ℝ (Fin d)) (σ r : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  lgDensity abar σ r x / ∫ y, lgDensity abar σ r y

/-- The `(σ, r)`-Laplace–Gaussian distribution `LG_d(ā, σ, r)` with mean `ā`. -/
noncomputable def lg {d : ℕ} (abar : EuclideanSpace ℝ (Fin d)) (σ r : ℝ) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  densityMeasure (lgPdf abar σ r)

end FriendlyShadow.Gaussian


