-- Prove2me | Definitions.Def_GoodHypotheses_Proper_Densities
-- name    : GoodHypotheses_Proper_Densities
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:14:13.505612+00:00
-- url     : https://prove2.me/theorems/17e47067-e493-4218-b249-eda80a47756f
-- title:
--   Probability densities, the generalized total variation distance, OPT, valid scores, Scheffé functions
-- statement:
--   Let $X$ be a measurable space with an arbitrary measure $\mu$ (no finiteness, $\sigma$-finiteness or standard-Borel assumption). A **probability density** is a measurable $f:X\to\mathbb R$ with $f\ge0$ everywhere, $f$ integrable and $\int f\,d\mu=1$; $f$ is **the density of a probability law** $P$ when $f$ is measurable, nonnegative and $P=f\cdot\mu$. For nonnegative integrable $f,g$ the **generalized total variation distance** (Definition 2) is
--   $$d_{TV}(f,g)=\tfrac12\int|f-g|\,d\mu .$$
--   For hypotheses $h_1,\dots,h_n$ and a target $p$, $\mathrm{OPT}=\min_{i\in[n]}d_{TV}(p,h_i)$ (Eq. (1)). Given $\varepsilon>0$, scores $\sigma_1,\dots,\sigma_n$ are **valid** (Definition 1) if $\sigma_i\le d_{TV}(h_i,p)+\varepsilon$ and $d_{TV}(h_i,h_j)\le\sigma_i+\sigma_j+\varepsilon$ for all $i,j$. A **Scheffé function** of $(f,g)$ (Definition 3) is $S:X\to[0,1]$ with $S=1$ where $f>g$ and $S=0$ where $f<g$, arbitrary in $[0,1]$ where $f=g$. The **importance-sampling statistic** of Fact 3.2 is $Z(x,y)=\frac{f(x)}{\psi(x)}S(x)-\frac{g(y)}{\omega(y)}S(y)+\frac12\big(\frac{g(y)}{\omega(y)}-\frac{f(x)}{\psi(x)}\big)$.
--
--   **Formalization Note.** Densities are real-valued; integrals are Bochner integrals, so every statement carries integrability. Indices are `Fin n` (0-based). $\mathrm{OPT}$ is the infimum over the finite index set, a minimum for $n\ge1$. Lean division gives $a/0=0$.
-- source:
--   Aamand, Aliakbarpour, Chen, Silwal, Stevens, Zou, A Good Way to Find Good Hypotheses, STOC 2027 submission (manuscript sha256 a428fbe0…), p. 1 Eq. (1); pp. 4–5 Definition 1; p. 6 Definition 2; p. 13 Definition 3; p. 14 Fact 3.2

import Mathlib

open MeasureTheory

namespace GoodHypotheses.Proper

/-!
# Densities, the generalized total variation distance, OPT, valid scores, Scheffé functions

Aamand, Aliakbarpour, Chen, Silwal, Stevens, Zou, *A Good Way to Find Good Hypotheses*,
STOC 2027 submission (manuscript sha256 a428fbe0…), p. 1 Eq. (1), p. 4–5 Definition 1,
p. 6 Definition 2, p. 13 Definition 3, p. 14 Fact 3.2.

* `X` is an arbitrary measurable space and `μ` an arbitrary measure on it (no finiteness,
  σ-finiteness or standard-Borel condition). Densities are real-valued functions on `X`.
* A **nonnegative integrable density** (a "proxy", p. 6) is a function `f : X → ℝ` with
  `∀ x, 0 ≤ f x` and `Integrable f μ`; statements carry these as hypotheses.
* `tvDist μ f g = (1/2) ∫ |f − g| dμ` (Definition 2), a Bochner integral; it is the usual total
  variation distance when `f, g` are probability densities.
* Hypothesis indices are `Fin n` (the paper's `[n]`, shifted to start at `0`).
-/

/-- `f` is a probability density with respect to `μ`: measurable, nonnegative everywhere,
integrable, with `∫ f dμ = 1`. -/
def IsProbDensity {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) : Prop :=
  Measurable f ∧ (∀ x, 0 ≤ f x) ∧ Integrable f μ ∧ ∫ x, f x ∂μ = 1

/-- `f` is a density of the probability law `P` with respect to `μ`: `f` is measurable and
nonnegative and `P = f · μ`. (Then `f` is a probability density, and a draw `X ∼ f` means
a draw from `P`.) -/
def IsDensityOf {X : Type*} [MeasurableSpace X] (μ : Measure X) (P : ProbabilityMeasure X)
    (f : X → ℝ) : Prop :=
  Measurable f ∧ (∀ x, 0 ≤ f x) ∧
    (P : Measure X) = μ.withDensity (fun x => ENNReal.ofReal (f x))

/-- The generalized total variation distance of Definition 2 (p. 6):
`dTV(f, g) = (1/2) ∫ |f − g| dμ`. -/
noncomputable def tvDist {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ) : ℝ :=
  (1 / 2) * ∫ x, |f x - g x| ∂μ

/-- `OPT = min_{i ∈ [n]} dTV(p, h_i)` (Eq. (1), p. 1). For `n ≥ 1` the index set is finite and
nonempty, so the infimum is a minimum. -/
noncomputable def OPT {X : Type*} [MeasurableSpace X] {n : ℕ} (μ : Measure X) (p : X → ℝ)
    (h : Fin n → X → ℝ) : ℝ :=
  ⨅ i, tvDist μ p (h i)

/-- Valid scores (Definition 1, pp. 4–5) for the parameter `ε`: underestimation (4)
`σ_i ≤ dTV(h_i, p) + ε` and the triangle inequality (5) `dTV(h_i, h_j) ≤ σ_i + σ_j + ε`,
for all `i, j`. -/
def ValidScores {X : Type*} [MeasurableSpace X] {n : ℕ} (μ : Measure X) (p : X → ℝ)
    (h : Fin n → X → ℝ) (ε : ℝ) (σ : Fin n → ℝ) : Prop :=
  (∀ i, σ i ≤ tvDist μ (h i) p + ε) ∧ (∀ i j, tvDist μ (h i) (h j) ≤ σ i + σ j + ε)

/-- `S` is a Scheffé function of `(f, g)` (Definition 3, p. 13): `S : X → [0, 1]`, `S x = 1`
where `f x > g x`, `S x = 0` where `f x < g x`, and arbitrary in `[0, 1]` where `f x = g x`. -/
def IsScheffe {X : Type*} (f g S : X → ℝ) : Prop :=
  ∀ x, 0 ≤ S x ∧ S x ≤ 1 ∧ (g x < f x → S x = 1) ∧ (f x < g x → S x = 0)

/-- The importance-sampling statistic of Fact 3.2 (p. 14), at `X = x`, `Y = y`:
`Z = (f(x)/ψ(x)) S(x) − (g(y)/ω(y)) S(y) + (1/2)(g(y)/ω(y) − f(x)/ψ(x))`
(Lean division: `a / 0 = 0`). -/
noncomputable def scheffeStatistic {X : Type*} (f g S ψ ω : X → ℝ) (x y : X) : ℝ :=
  f x / ψ x * S x - g y / ω y * S y + (1 / 2) * (g y / ω y - f x / ψ x)

end GoodHypotheses.Proper


