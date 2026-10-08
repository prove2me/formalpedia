-- Prove2me | Definitions.Def_PrescAnalytics_KNN_Basic
-- name    : PrescAnalytics_KNN_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:31:56.597026+00:00
-- url     : https://prove2.me/theorems/c0ca751d-4294-466a-9c63-e15cd5484b39
-- title:
--   Conditional problem (2), weighted SAA (3), kNN weights (12), Definition 1 and Assumptions 3–5
-- statement:
--   This file fixes the setting of Bertsimas and Kallus, *From Predictive to Prescriptive Analytics*: a decision $z\in\mathcal Z\subseteq\mathbb R^{d_z}$ is taken after observing covariates $X=x\in\mathbb R^{d_x}$ in order to minimize an uncertain cost $c(z;Y)$, $Y\in\mathbb R^{d_y}$. All three spaces carry the Euclidean norm. Let $\mu$ be the joint law of $(X,Y)$ and $\mu_X$ its first marginal.
--
--   1. **Conditional cost and the full-information problem (2).** For a fixed version $\mu_{Y|x}$ of the conditional law of $Y$ given $X=x$,
--   $$C(z\mid x)=\mathbb E\big[c(z;Y)\mid X=x\big]=\int c(z;y)\,\mu_{Y|x}(dy),\qquad \mathcal Z^*(x)=\Big\{z\in\mathcal Z:\ C(z\mid x)\le C(z'\mid x)\ \text{for all } z'\in\mathcal Z\Big\}.$$
--   The optimal value is $v^*(x)=C(z^\star\mid x)$ for any $z^\star\in\mathcal Z^*(x)$.
--   2. **Weighted sample average (3).** Given weights $w_{N,i}(x)$ and observations $y^1,y^2,\dots$,
--   $$\widehat C_N(z\mid x)=\sum_{i=1}^N w_{N,i}(x)\,c(z;y^i),\qquad \hat\mu_{Y|x,N}(A)=\sum_{i=1}^N w_{N,i}(x)\,\mathbb I[y^i\in A],$$
--   and the predictive prescription $\hat z_N(x)$ is any element of $\arg\min_{z\in\mathcal Z}\widehat C_N(z\mid x)$, a set that may be empty.
--   3. **kNN weights (12).** $w^{k\mathrm{NN}}_{N,i}(x)=\frac1k\,\mathbb I[x^i \text{ is one of the } k \text{ nearest neighbours of } x \text{ among } x^1,\dots,x^N]$, with ties among equidistant points broken by the lower-index-first rule. Theorem 5 uses $k=k_N=\min\{\lceil CN^\delta\rceil,\,N-1\}$.
--   4. **Assumption 3 (Existence).** $\mathbb E|c(z;Y)|<\infty$ for every $z\in\mathcal Z$, and $\mathcal Z^*(x)\neq\emptyset$ for $\mu_X$-almost every $x$.
--   5. **Assumption 4 (Continuity).** For every $z\in\mathcal Z$ and $\varepsilon>0$ there is $\delta>0$ with $|c(z;y)-c(z';y)|\le\varepsilon$ for all $z'\in\mathcal Z$ with $\|z-z'\|\le\delta$ and all $y\in\mathcal Y$.
--   6. **Assumption 5 (Regularity).** $\mathcal Z$ is closed and nonempty, and either (1) $\mathcal Z$ is bounded, or (2) $\liminf_{\|z\|\to\infty}\inf_{y\in\mathcal Y}c(z;y)>-\infty$ and for every $x\in\mathcal X$ there is $D_x\subseteq\mathcal Y$ with $c(z;y)\to\infty$ as $\|z\|\to\infty$ uniformly over $y\in D_x$ and $\mathbb P(Y\in D_x\mid X=x)>0$.
--   7. **Definition 1.** A prescription is *asymptotically optimal* if, with probability 1, for $\mu_X$-almost every $x$, $\lim_{N\to\infty}C(\hat z_N(x)\mid x)=v^*(x)$; it is *consistent* if, with probability 1, for $\mu_X$-almost every $x$, $\lim_{N\to\infty}\inf_{z\in\mathcal Z^*(x)}\|\hat z_N(x)-z\|=0$.
--
--   These are the objects in which Theorem 5 and Lemmas 5–7 of the paper are stated.
--
--   **Formalization Note** The spaces are `EuclideanSpace ℝ (Fin d)`, so the kNN distance and $\|z-z'\|$ are Euclidean (on `Fin d → ℝ` Lean would use the sup norm and a different set of neighbours). $\mathcal X,\mathcal Y$ are sets on which $X$, $Y$ lie almost surely; they enter as parameters. $\mu_{Y|x}$ is Mathlib's disintegration `μ.condKernel x`, a fixed version of the conditional law; $C(z\mid x)$ is its Bochner integral, which is $0$ when $c(z;\cdot)$ is not integrable under it. $v^*$ is not defined as a real infimum (which would be $0$ when unbounded below): the optimal value is read through elements of $\mathcal Z^*(x)$. Samples are indexed $0,\dots,N-1$ for the paper's $1,\dots,N$. The neighbour rank of $i$ is the number of $j<N$ that are strictly closer to $x$, or equally close with $j<i$; $x^i$ is a kNN when this rank is $<k$. This is the lower-index-first rule of p. 10; with it, for $1\le k\le N$ the weights are nonnegative and sum to $1$ (eq. (5)'s set $\{i:\sum_j\mathbb I[\|x-x_i\|\ge\|x-x_j\|]\le k\}$ is not used, since with ties it has fewer than $k$ elements). In $\mathbb N$, $N-1=0$ at $N=0$, so $k_0=k_1=0$ and $1/0=0$ makes all weights vanish for $N\le1$. Assumption 4's $z'$ ranges over $\mathcal Z$ (the paper: all $z'$), since $c$ only matters on $\mathcal Z$. Case 2 of Assumption 5 is written with explicit quantifiers: $\exists B,R$ with $c(z;y)\ge B$ for $z\in\mathcal Z$, $\|z\|\ge R$, $y\in\mathcal Y$; and for each $x\in\mathcal X$ a measurable $D\subseteq\mathcal Y$ with `μ.condKernel x D > 0` and, for every $M$, an $R$ with $c(z;y)\ge M$ for $z\in\mathcal Z$, $\|z\|\ge R$, $y\in D$. Measurability of $D_x$ is implicit in the paper's $\mathbb P(Y\in D_x\mid X=x)$, and "for every $x\in\mathcal X$" refers to the version `μ.condKernel`. Definition 1 is stated for a set-valued prescription rule `zhat N ω x`: almost surely, for $\mu_X$-a.e. $x$, $\mathcal Z^*(x)$ is nonempty, the prescription is nonempty for all large $N$, and **every** sequence $z_N$ lying in `zhat N ω x` for all large $N$ satisfies $C(z_N\mid x)\to C(z^\star\mid x)$ for every $z^\star\in\mathcal Z^*(x)$ (resp. `Metric.infDist z_N (𝒵*(x)) → 0`), with the quantifier order "with probability 1, for $\mu_X$-a.e. $x$". `Metric.infDist` to the empty set is $0$; this is harmless because $\mathcal Z^*(x)\neq\emptyset$ for a.e. $x$ under Assumption 3.
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, pp. 2–3, 10, 18–19, 44, Eqs. (2), (3), (12), Definition 1, Assumptions 3–5, and the notation of §9.3

import Mathlib

namespace PrescAnalytics.KNN

open MeasureTheory ProbabilityTheory Filter Topology

/-! Setting of Bertsimas–Kallus, *From Predictive to Prescriptive Analytics*, arXiv:1402.5481v4:
covariates `x ∈ ℝ^{d_x}`, uncertainty `y ∈ ℝ^{d_y}` and decisions `z ∈ ℝ^{d_z}`, all with the
Euclidean norm; `μ` is the joint law of `(X, Y)`. -/

/-- The conditional expected cost `C(z|x) = E[c(z; Y) | X = x]` (p. 44), taken against the fixed
version `μ.condKernel x` of the conditional law `μ_{Y|x}` of `Y` given `X = x`. -/
noncomputable def condCost {dx dy dz : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))) [IsFiniteMeasure μ]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (z : EuclideanSpace ℝ (Fin dz)) (x : EuclideanSpace ℝ (Fin dx)) : ℝ :=
  ∫ y, c z y ∂(μ.condKernel x)

/-- The full-information optimal set `𝒵*(x) = argmin_{z ∈ 𝒵} C(z|x)` of problem (2) (p. 2): the
decisions in `𝒵` whose conditional cost is no larger than that of any other decision in `𝒵`.
It may be empty. -/
def optSet {dx dy dz : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))) [IsFiniteMeasure μ]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz))) (x : EuclideanSpace ℝ (Fin dx)) :
    Set (EuclideanSpace ℝ (Fin dz)) :=
  {z | z ∈ Z ∧ ∀ z' ∈ Z, condCost μ c z x ≤ condCost μ c z' x}

/-- The weighted sample mean `∑_{i=1}^N w_{N,i} h(y^i)` of a function `h` of the uncertainty, for
weights `w N i` and observations `ys i`. Samples are indexed `0, …, N-1` (the paper's `1, …, N`). -/
def weightedMean {dy : ℕ} (w : ℕ → ℕ → ℝ) (ys : ℕ → EuclideanSpace ℝ (Fin dy))
    (h : EuclideanSpace ℝ (Fin dy) → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, w N i * h (ys i)

/-- The weighted sample cost `Ĉ_N(z|x) = ∑_{i=1}^N w_{N,i}(x) c(z; y^i)` (p. 44), the objective of
the predictive prescription (3), for the weights `w N i = w_{N,i}(x)` at a fixed covariate `x`. -/
def weightedCost {dy dz : ℕ} (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (w : ℕ → ℕ → ℝ) (ys : ℕ → EuclideanSpace ℝ (Fin dy)) (N : ℕ)
    (z : EuclideanSpace ℝ (Fin dz)) : ℝ :=
  weightedMean w ys (c z) N

/-- The weighted empirical conditional distribution `μ̂_{Y|x,N}(A) = ∑_{i=1}^N w_{N,i}(x) 𝕀[y^i ∈ A]`
(p. 44), as a set function. -/
noncomputable def weightedMeasure {dy : ℕ} (w : ℕ → ℕ → ℝ) (ys : ℕ → EuclideanSpace ℝ (Fin dy)) (N : ℕ)
    (A : Set (EuclideanSpace ℝ (Fin dy))) : ℝ :=
  weightedMean w ys (A.indicator 1) N

/-- The set `argmin_{z ∈ 𝒵} Ĉ_N(z|x)` of the predictive prescription (3) (p. 3); it may be empty. -/
def weightedArgmin {dy dz : ℕ} (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (w : ℕ → ℕ → ℝ) (ys : ℕ → EuclideanSpace ℝ (Fin dy)) (Z : Set (EuclideanSpace ℝ (Fin dz)))
    (N : ℕ) : Set (EuclideanSpace ℝ (Fin dz)) :=
  {z | z ∈ Z ∧ ∀ z' ∈ Z, weightedCost c w ys N z ≤ weightedCost c w ys N z'}

/-- The neighbour rank of the data point `i` among the first `N` covariates `xs 0, …, xs (N-1)`
with respect to the query `x`: the number of indices `j < N` whose covariate is strictly closer
to `x` than `xs i`, or equally close with a smaller index (the lower-index-first tie rule, p. 10). -/
noncomputable def knnRank {dx : ℕ} (xs : ℕ → EuclideanSpace ℝ (Fin dx)) (x : EuclideanSpace ℝ (Fin dx))
    (N i : ℕ) : ℕ :=
  ((Finset.range N).filter fun j =>
    dist x (xs j) < dist x (xs i) ∨ (dist x (xs j) = dist x (xs i) ∧ j < i)).card

/-- `x^i` is one of the `k` nearest neighbours of `x` among the first `N` data points, ties among
equidistant points broken by the lower-index-first rule (p. 10). -/
def IsKNN {dx : ℕ} (k : ℕ) (xs : ℕ → EuclideanSpace ℝ (Fin dx)) (x : EuclideanSpace ℝ (Fin dx))
    (N i : ℕ) : Prop :=
  i < N ∧ knnRank xs x N i < k

/-- The kNN weights (12) (p. 10): `w^{kNN}_{N,i}(x) = (1/k) 𝕀[x^i is a kNN of x]`. -/
noncomputable def knnWeightK {dx : ℕ} (k : ℕ) (xs : ℕ → EuclideanSpace ℝ (Fin dx))
    (x : EuclideanSpace ℝ (Fin dx)) (N i : ℕ) : ℝ :=
  open Classical in
  if IsKNN k xs x N i then (k : ℝ)⁻¹ else 0

/-- The neighbourhood size of Theorem 5 (p. 19): `k_N = min {⌈C N^δ⌉, N - 1}`. In ℕ, `N - 1 = 0`
at `N = 0`, so `k_0 = k_1 = 0` and all weights vanish for `N ≤ 1`. -/
noncomputable def kSeq (C δ : ℝ) (N : ℕ) : ℕ :=
  min ⌈C * (N : ℝ) ^ δ⌉₊ (N - 1)

/-- The kNN weights (12) with `k = k_N` of Theorem 5: `knnWeight C δ xs x N i = w_{N,i}(x)`. -/
noncomputable def knnWeight {dx : ℕ} (C δ : ℝ) (xs : ℕ → EuclideanSpace ℝ (Fin dx))
    (x : EuclideanSpace ℝ (Fin dx)) (N i : ℕ) : ℝ :=
  knnWeightK (kSeq C δ N) xs x N i

/-- The kNN predictive prescription set (3) with weights (12), `k = k_N`: on the data path
`S · ω = ((x^1, y^1), (x^2, y^2), …)` and at the query `x`, the set
`argmin_{z ∈ 𝒵} ∑_{i=1}^N w^{kNN}_{N,i}(x) c(z; y^i)`. -/
noncomputable def knnArgmin {Ω : Type*} {dx dy dz : ℕ} (C δ : ℝ)
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz)))
    (S : ℕ → Ω → EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))
    (N : ℕ) (ω : Ω) (x : EuclideanSpace ℝ (Fin dx)) : Set (EuclideanSpace ℝ (Fin dz)) :=
  weightedArgmin c (knnWeight C δ (fun i => (S i ω).1) x) (fun i => (S i ω).2) Z N

/-- **Assumption 3 (Existence)** (p. 18): `E[|c(z; Y)|] < ∞` for every `z ∈ 𝒵`, and `𝒵*(x) ≠ ∅` for
`μ_X`-almost every `x`. -/
def Assumption3 {dx dy dz : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))) [IsFiniteMeasure μ]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz))) : Prop :=
  (∀ z ∈ Z, Integrable (fun p => c z p.2) μ) ∧
    ∀ᵐ x ∂(μ.map Prod.fst), (optSet μ c Z x).Nonempty

/-- **Assumption 4 (Continuity)** (p. 18): `c(z; y)` is equicontinuous in `z`: for any `z ∈ 𝒵` and
`ε > 0` there is `δ > 0` with `|c(z; y) - c(z'; y)| ≤ ε` for all `z' ∈ 𝒵` with `‖z - z'‖ ≤ δ` and
all `y ∈ 𝒴`. -/
def Assumption4 {dy dz : ℕ} (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz))) (Ys : Set (EuclideanSpace ℝ (Fin dy))) : Prop :=
  ∀ z ∈ Z, ∀ ε > 0, ∃ δ > 0, ∀ z' ∈ Z, ‖z - z'‖ ≤ δ → ∀ y ∈ Ys, |c z y - c z' y| ≤ ε

/-- First half of case 2 of Assumption 5 (p. 19): `liminf_{‖z‖→∞} inf_{y ∈ 𝒴} c(z; y) > -∞`, i.e.
there are `B` and `R` with `c(z; y) ≥ B` whenever `z ∈ 𝒵`, `‖z‖ ≥ R` and `y ∈ 𝒴`. -/
def CostBoundedBelowAtInfinity {dy dz : ℕ}
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz))) (Ys : Set (EuclideanSpace ℝ (Fin dy))) : Prop :=
  ∃ B R : ℝ, ∀ z ∈ Z, R ≤ ‖z‖ → ∀ y ∈ Ys, B ≤ c z y

/-- `c(z; y) → ∞` as `‖z‖ → ∞` (over `z ∈ 𝒵`), uniformly over `y ∈ D` (case 2 of Assumption 5). -/
def CoerciveUniformlyOn {dy dz : ℕ}
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz))) (D : Set (EuclideanSpace ℝ (Fin dy))) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, ∀ z ∈ Z, R ≤ ‖z‖ → ∀ y ∈ D, M ≤ c z y

/-- **Assumption 5 (Regularity)** (pp. 18–19): `𝒵` is closed and nonempty, and either (1) `𝒵` is
bounded, or (2) `liminf_{‖z‖→∞} inf_{y ∈ 𝒴} c(z; y) > -∞` and for every `x ∈ 𝒳` there is a
(measurable) `D_x ⊆ 𝒴` with `c(z; y) → ∞` as `‖z‖ → ∞` uniformly over `y ∈ D_x` and
`P(Y ∈ D_x | X = x) > 0`, the conditional probability read in the version `μ.condKernel x`. -/
def Assumption5 {dx dy dz : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))) [IsFiniteMeasure μ]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz))) (Xs : Set (EuclideanSpace ℝ (Fin dx)))
    (Ys : Set (EuclideanSpace ℝ (Fin dy))) : Prop :=
  IsClosed Z ∧ Z.Nonempty ∧
    (Bornology.IsBounded Z ∨
      (CostBoundedBelowAtInfinity c Z Ys ∧
        ∀ x ∈ Xs, ∃ D ⊆ Ys, MeasurableSet D ∧ 0 < μ.condKernel x D ∧ CoerciveUniformlyOn c Z D))

/-- **Definition 1, asymptotic optimality** (p. 18), for a set-valued prescription rule
`zhat N ω x ⊆ ℝ^{d_z}` (the decisions the rule may return on the data path `ω` at `x`): with
probability 1, for `μ_X`-almost every `x`, the full-information optimizer exists, the prescription is eventually defined, and every
sequence `z_N` chosen from `zhat N ω x` for all large `N` satisfies
`lim_N E[c(z_N; Y) | X = x] = v*(x)`, i.e. `C(z_N|x) → C(z⋆|x)` for every
`z⋆ ∈ 𝒵*(x)`. -/
def IsAsymptoticallyOptimal {Ω : Type*} [MeasurableSpace Ω] {dx dy dz : ℕ} (P : Measure Ω)
    (μ : Measure (EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))) [IsFiniteMeasure μ]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz)))
    (zhat : ℕ → Ω → EuclideanSpace ℝ (Fin dx) → Set (EuclideanSpace ℝ (Fin dz))) : Prop :=
  ∀ᵐ ω ∂P, ∀ᵐ x ∂(μ.map Prod.fst),
    (optSet μ c Z x).Nonempty ∧
      (∀ᶠ N in atTop, (zhat N ω x).Nonempty) ∧
      ∀ zN : ℕ → EuclideanSpace ℝ (Fin dz),
        (∀ᶠ N in atTop, zN N ∈ zhat N ω x) →
          ∀ zstar ∈ optSet μ c Z x,
            Tendsto (fun N => condCost μ c (zN N) x) atTop (𝓝 (condCost μ c zstar x))

/-- **Definition 1, consistency** (p. 18), for a set-valued prescription rule: with probability 1,
for `μ_X`-almost every `x`, the full-information optimizer exists, the prescription is eventually defined and every sequence `z_N`
chosen from `zhat N ω x` for all large `N` satisfies
`lim_N inf_{z ∈ 𝒵*(x)} ‖z_N - z‖ = 0`. (`Metric.infDist` to the empty set is `0`.) -/
def IsConsistent {Ω : Type*} [MeasurableSpace Ω] {dx dy dz : ℕ} (P : Measure Ω)
    (μ : Measure (EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))) [IsFiniteMeasure μ]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz)))
    (zhat : ℕ → Ω → EuclideanSpace ℝ (Fin dx) → Set (EuclideanSpace ℝ (Fin dz))) : Prop :=
  ∀ᵐ ω ∂P, ∀ᵐ x ∂(μ.map Prod.fst),
    (optSet μ c Z x).Nonempty ∧
      (∀ᶠ N in atTop, (zhat N ω x).Nonempty) ∧
      ∀ zN : ℕ → EuclideanSpace ℝ (Fin dz),
        (∀ᶠ N in atTop, zN N ∈ zhat N ω x) →
          Tendsto (fun N => Metric.infDist (zN N) (optSet μ c Z x)) atTop (𝓝 0)

end PrescAnalytics.KNN


