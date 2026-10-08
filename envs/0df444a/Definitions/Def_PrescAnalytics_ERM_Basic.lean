-- Prove2me | Definitions.Def_PrescAnalytics_ERM_Basic
-- name    : PrescAnalytics_ERM_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:31:57.580081+00:00
-- url     : https://prove2.me/theorems/09ddeb0b-d738-4ff1-ac72-b70861bba15c
-- title:
--   Definition 3 — multivariate Rademacher complexities ℜ̂_N(F; S_N), ℜ_N(F); expected and empirical cost of a decision rule
-- statement:
--   This file fixes the objects of §8.2 of Bertsimas and Kallus, *From Predictive to Prescriptive Analytics*: decision rules $z(\cdot):\mathcal X\to\mathbb R^{d}$, their expected and empirical costs, and the multivariate Rademacher complexity of a class of such rules.
--
--   1. **Rademacher signs.** A sign $\sigma\in\{+1,-1\}$; a sign matrix $\sigma=(\sigma_{ik})\in\{\pm1\}^{N\times d}$.
--   2. **Empirical multivariate Rademacher complexity** (Definition 3). For a class $\mathcal F$ of functions $g$ from a set $\mathcal U$ to $\mathbb R^d$ and a sample $S_N=(s_1,\dots,s_N)\in\mathcal U^N$,
--   $$\widehat{\mathfrak R}_N(\mathcal F;S_N)=\mathbb E_\sigma\Big[\frac2N\sup_{g\in\mathcal F}\sum_{i=1}^N\sum_{k=1}^d\sigma_{ik}\,g_k(s_i)\Big],$$
--   where the $\sigma_{ik}$ are independent and uniform on $\{+1,-1\}$; the expectation is the average over all $2^{Nd}$ sign matrices. There is no absolute value inside the supremum, and the factor is $2/N$.
--   3. **Marginal multivariate Rademacher complexity** (Definition 3). For a probability measure $\nu$ on $\mathcal U$, $\mathfrak R_N(\mathcal F)=\mathbb E_{S_N\sim\nu^N}\big[\widehat{\mathfrak R}_N(\mathcal F;S_N)\big]$, the expectation over an i.i.d. sample.
--   4. **Univariate complexities.** For a class $\mathcal G$ of real-valued functions, $\widehat{\mathfrak R}_N(\mathcal G;S_N)$ and $\mathfrak R_N(\mathcal G)$ are the case $d=1$, which the paper notes coincides with the common definition.
--   5. **Cost class.** For a cost $c(z;y)$ with decisions $z\in\mathbb R^d$ and a class $\mathcal F$ of decision rules, $\mathcal G=\{(x,y)\mapsto c(f(x);y):f\in\mathcal F\}$.
--   6. **Expected and empirical cost.** For a probability measure $\mu$ on $\mathcal X\times\mathcal Y$ and a sample $S_N=((x^1,y^1),\dots,(x^N,y^N))$,
--   $$\mathbb E[c(z(X);Y)]=\int c(z(x);y)\,d\mu(x,y),\qquad \frac1N\sum_{i=1}^N c(z(x^i);y^i).$$
--   The empirical cost is the objective of the empirical-risk-minimization problem (4); the empirical mean $\frac1N\sum_i g(u^i)$ of a real function is defined the same way.
--   7. **Pointwise separable class.** A class $\mathcal F$ of functions is pointwise separable when some countable subclass $\mathcal F_0\subseteq\mathcal F$ has every $f\in\mathcal F$ as a pointwise limit of a sequence in $\mathcal F_0$. This is the standard measurability convention under which the suprema over $\mathcal F$ whose probabilities and expectations the paper takes are measurable; the linear rules (25) satisfy it.
--
--   The multivariate complexity measures the richness of a class of vector-valued decision rules; Theorem 13 bounds out-of-sample cost by empirical cost plus a multiple of it.
--
--   **Formalization Note** Decisions live in `Fin d → ℝ`, whose Lean norm is the sup norm $\max_k|z_k|$, the $\infty$-norm of Lemma 1. For each sign matrix the supremum is taken in `EReal`, so an unbounded class gives $+\infty$ (not a junk $0$) and an empty class gives $-\infty$; the empirical complexity is then a nonnegative real multiple of a finite sum in `EReal`. The marginal complexity is the lower Lebesgue integral, in $[0,\infty]$, of the empirical complexity clipped at $0$; for a nonempty class the empirical complexity is $\ge 0$ (average over $\sigma$ of the sup is at least the sup of the average, which is $0$), so the clipping loses nothing. The univariate complexities are Definition 3 applied to the class lifted to `Fin 1 → ℝ`. The expected cost is a Bochner integral; the theorems that use it assume what makes it the paper's expectation (bounded, measurable integrand).
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, pp. 3, 37, 39–41, Eq. (4), Definition 3, Lemma 1 (class 𝒢), proof of Theorem 13

import Mathlib

namespace PrescAnalytics.ERM

open MeasureTheory Filter Topology

/-- A Rademacher sign `σ ∈ {+1, −1}` encoded by a Boolean: `true ↦ +1`, `false ↦ −1`. -/
def signOf (b : Bool) : ℝ := if b then 1 else -1

/-- For a fixed sign matrix `σ ∈ {±1}^{N×d}` and a sample `s = (s_1, …, s_N)`, the supremum
`sup_{g ∈ F} Σ_{i=1}^N Σ_{k=1}^d σ_{ik} g_k(s_i)` (Definition 3, p. 39), computed in `EReal`:
it is `+∞` when the sums are unbounded above over `F`, and `−∞` when `F` is empty. -/
noncomputable def signedSup {U : Type*} {d N : ℕ} (F : Set (U → Fin d → ℝ)) (s : Fin N → U)
    (σ : Fin N → Fin d → Bool) : EReal :=
  ⨆ g ∈ F, ((∑ i, ∑ k, signOf (σ i k) * g (s i) k : ℝ) : EReal)

/-- Definition 3 (p. 39): the empirical multivariate Rademacher complexity
`ℜ̂_N(F; S_N) = E_σ[(2/N) sup_{g ∈ F} Σ_i Σ_k σ_{ik} g_k(s_i)]` of a class `F` of `ℝ^d`-valued
functions on the sample `s`, where the `σ_{ik}` are i.i.d. uniform signs: the expectation is the
average over all `2^{N d}` sign matrices. Factor `2/N`, no absolute value; value in `EReal`. -/
noncomputable def empRademacher {U : Type*} {d N : ℕ} (F : Set (U → Fin d → ℝ))
    (s : Fin N → U) : EReal :=
  (((2 : ℝ) / N / 2 ^ (N * d) : ℝ) : EReal) * ∑ σ : Fin N → Fin d → Bool, signedSup F s σ

/-- Definition 3 (p. 39): the marginal multivariate Rademacher complexity
`ℜ_N(F) = E[ℜ̂_N(F; S_N)]`, the expectation over an i.i.d. sample `S_N ∼ ν^N`, as a lower Lebesgue
integral in `ℝ≥0∞` of the empirical complexity (which is `≥ 0` for a nonempty class). -/
noncomputable def margRademacher {U : Type*} [MeasurableSpace U] {d : ℕ} (ν : Measure U) (N : ℕ)
    (F : Set (U → Fin d → ℝ)) : ENNReal :=
  ∫⁻ s, (empRademacher F s).toENNReal ∂(Measure.pi fun _ : Fin N => ν)

/-- A real-valued class `G` viewed as a class of `ℝ^1`-valued functions `u ↦ (g u)`. -/
def liftClass {U : Type*} (G : Set (U → ℝ)) : Set (U → Fin 1 → ℝ) :=
  (fun g u _ => g u) '' G

/-- The univariate empirical Rademacher complexity `ℜ̂_N(G; S_N)` of a real-valued class: Definition 3
with `d = 1` ("when `d = 1` the above definition coincides with the common definition", p. 39). -/
noncomputable def empRademacherR {U : Type*} {N : ℕ} (G : Set (U → ℝ)) (s : Fin N → U) : EReal :=
  empRademacher (liftClass G) s

/-- The univariate marginal Rademacher complexity `ℜ_N(G)`: Definition 3 with `d = 1`. -/
noncomputable def margRademacherR {U : Type*} [MeasurableSpace U] (ν : Measure U) (N : ℕ)
    (G : Set (U → ℝ)) : ENNReal :=
  margRademacher ν N (liftClass G)

/-- The empirical mean `(1/N) Σ_{i=1}^N g(u^i)` of `g` on the sample `s = (u^1, …, u^N)`. -/
noncomputable def empMean {U : Type*} {N : ℕ} (s : Fin N → U) (g : U → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, g (s i)

/-- The cost class `𝒢 = {(x, y) ↦ c(f(x); y) : f ∈ F}` of Lemma 1 (p. 40) and of the proof of
Theorem 13 (p. 41), for a cost `c(z; y)` with decisions `z ∈ ℝ^d`. -/
def costClass {X Y : Type*} {d : ℕ} (c : (Fin d → ℝ) → Y → ℝ) (F : Set (X → Fin d → ℝ)) :
    Set (X × Y → ℝ) :=
  {g | ∃ f ∈ F, g = fun p => c (f p.1) p.2}

/-- The expected cost `E[c(z(X); Y)] = ∫ c(z(x); y) dμ(x, y)` of a decision rule `z(·)` (Bochner
integral; integrable when `c` is bounded and measurable and `z` is measurable). -/
noncomputable def expCost {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {d : ℕ}
    (μ : Measure (X × Y)) (c : (Fin d → ℝ) → Y → ℝ) (z : X → Fin d → ℝ) : ℝ :=
  ∫ p, c (z p.1) p.2 ∂μ

/-- The empirical cost `(1/N) Σ_{i=1}^N c(z(x^i); y^i)` of a decision rule on the sample
`s = ((x^1, y^1), …, (x^N, y^N))`, the objective of (4). -/
noncomputable def empCost {X Y : Type*} {d N : ℕ} (s : Fin N → X × Y)
    (c : (Fin d → ℝ) → Y → ℝ) (z : X → Fin d → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, c (z (s i).1) (s i).2

/-- A class `F` of functions `U → V` is *pointwise separable* when it has a countable subclass `F₀`
such that every `f ∈ F` is the pointwise limit of a sequence in `F₀`. This is the standard
measurability convention under which the suprema over `F` that the paper takes expectations and
probabilities of are measurable (it holds for the linear rules (25)). -/
def IsPointwiseSeparable {U V : Type*} [TopologicalSpace V] (F : Set (U → V)) : Prop :=
  ∃ F₀ ⊆ F, F₀.Countable ∧ ∀ f ∈ F, ∃ u : ℕ → U → V, (∀ n, u n ∈ F₀) ∧
    ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (f x))

end PrescAnalytics.ERM


