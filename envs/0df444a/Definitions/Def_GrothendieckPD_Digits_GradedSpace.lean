-- Prove2me | Definitions.Def_GrothendieckPD_Digits_GradedSpace
-- name    : GrothendieckPD_Digits_GradedSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:53.035361+00:00
-- url     : https://prove2.me/theorems/30af5d82-621d-4129-84cc-494b1a676bc3
-- title:
--   §3: the graded Gaussian space, graded projections $\langle\Pi_d f,\Pi_d g\rangle$, chaos spaces $\overline{\mathcal H}_d$ and the set $\mathcal K$
-- statement:
--   Let $X=(X^{(d)}_i)$ be a family of independent standard Gaussian variables, countably many of each grade $d\ge1$; $X_1,X_2,\dots$ denote the grade-one variables. For a finitely supported multi-index $\alpha$ its total grade is $\mathrm{gr}(\alpha)=\sum_{v}\mathrm{grade}(v)\,\alpha_v$, $\psi_\alpha(X)=\prod_v\psi_{\alpha_v}(X_v)$, and $\hat f_\alpha=\mathbb E[f(X)\psi_\alpha(X)]$.
--
--   1. **Graded projections.** $\Pi_d$ projects $L^2(X)$ onto the span of the Hermite polynomials of total grade $d$, so
--   $$c_d(f,g)=\langle\Pi_df,\Pi_dg\rangle=\sum_{\mathrm{gr}(\alpha)=d}\hat f_\alpha\hat g_\alpha .$$
--   2. **Chaos spaces.** $\overline{\mathcal H}_d$ is the closure in $L^2(X)$ of the span of $\{\mathrm{He}_\alpha(X):\mathrm{gr}(\alpha)=d\}$ (Eq. 3.4); $\mathcal H_d(X_1,\dots,X_n)$ is the degree-$d$ Gaussian chaos of the first $n$ grade-one variables.
--   3. **Oddness.** The graded sign transformation is $\tilde X^{(d)}_i=(-1)^dX^{(d)}_i$; $f$ is odd when $f(\tilde X)=-f(X)$ almost surely.
--   4. **Asymptotic Boolean functions.** $f\in L^2(X)$ with $f(X)\in\{-1,1\}$ almost surely.
--   5. **The set $\mathcal K$ of Lemma 3.3.** All sequences $c(\mu)=(\mathbb E_{(f,g)\sim\mu}c_m(f,g))_m$ for distributions $\mu$ on pairs of odd asymptotic Boolean functions.
--
--   The graded space is the limit object in which Krivine rounding schemes and their optimizers are attained; the upper-bound certificate of Section 4.2 is built on it.
--
--   **Formalization Note** The variables are the coordinates of $\mathbb N_{+}\times\mathbb N\to\mathbb R$ under the product of standard Gaussians; $X^{(d)}_i$ is coordinate $(d,i)$. Membership in $\overline{\mathcal H}_d$ is written through the Hermite expansion ($f\in L^2$ and $\hat f_\alpha=0$ unless $\mathrm{gr}(\alpha)=d$), which is equivalent because $\{\psi_\alpha\}$ is an orthonormal basis of $L^2(X)$ (p. 7). Distributions on pairs of functions are jointly measurable random pairs.
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, §3 pp. 7–8: graded Gaussian space, Eq. (3.2)–(3.4), §3.2 (asymptotic Boolean functions), Lemma 3.3 (𝒦)

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_FiniteGames
open MeasureTheory ProbabilityTheory

namespace GrothendieckPD.Digits

/-- The variables of the graded Gaussian space (§3.1, pp. 7–8): the variable `X_i^{(d)}` of
grade `d ≥ 1` and index `i` is the pair `(d, i)`. Every grade carries countably many variables.
The grade-1 variables `X_1, X_2, …` of the paper are `(1, 1), (1, 2), …`. -/
abbrev GVar := ℕ+ × ℕ

/-- A point of the graded space: a value of every variable. -/
abbrev GPoint := GVar → ℝ

/-- The law of `X`: all variables i.i.d. standard Gaussian, regardless of grade (p. 7). -/
noncomputable def gradedGaussian : Measure GPoint :=
  Measure.infinitePi fun _ : GVar => gaussianReal 0 1

/-- The total grade `gr(α) = ∑_v grade(v) · α_v` of a finitely supported multi-index `α`. -/
def grade (α : GVar →₀ ℕ) : ℕ :=
  α.sum fun v k => (v.1 : ℕ) * k

/-- `ψ_α(X) = ∏_v ψ_{α_v}(X_v)`, the orthonormal Hermite basis function of `L²(X)`. -/
noncomputable def psiMulti (α : GVar →₀ ℕ) (x : GPoint) : ℝ :=
  α.prod fun v k => psi k (x v)

/-- The Hermite coefficient `f̂_α = E[f(X) ψ_α(X)]`. -/
noncomputable def hcoeff (f : GPoint → ℝ) (α : GVar →₀ ℕ) : ℝ :=
  ∫ x, f x * psiMulti α x ∂gradedGaussian

/-- `c_d(f,g) = ⟨Π_d f, Π_d g⟩ = ∑_{gr(α) = d} f̂_α ĝ_α`, the inner product of the graded-degree-`d`
parts (Π_d projects onto the span of the graded-degree-`d` Hermite polynomials, p. 7). The sum
is over the countable set of multi-indices of total grade `d`. -/
noncomputable def gradedInner (d : ℕ) (f g : GPoint → ℝ) : ℝ :=
  ∑' α : {α : GVar →₀ ℕ // grade α = d}, hcoeff f α * hcoeff g α

/-- Membership in `𝐇_d = closure of span{He_α(X) : gr(α) = d}` in `L²(X)` (Eq. 3.4, p. 8),
written through the Hermite expansion: `p ∈ L²(X)` and `p̂_α = 0` whenever `gr(α) ≠ d`. -/
def InChaos (d : ℕ) (p : GPoint → ℝ) : Prop :=
  MemLp p 2 gradedGaussian ∧ ∀ α : GVar →₀ ℕ, grade α ≠ d → hcoeff p α = 0

/-- Membership in `H_d(X_1, …, X_n)`, the degree-`d` Gaussian chaos of the first `n` grade-1
variables (p. 7): `p ∈ L²(X)` and `p̂_α ≠ 0` only for `α` supported on `X_1, …, X_n` with
`|α| = d`. -/
def InFinitaryChaos (d n : ℕ) (p : GPoint → ℝ) : Prop :=
  MemLp p 2 gradedGaussian ∧ ∀ α : GVar →₀ ℕ, hcoeff p α ≠ 0 →
    grade α = d ∧ ∀ v ∈ α.support, (v.1 : ℕ) = 1 ∧ 1 ≤ v.2 ∧ v.2 ≤ n

/-- The graded sign transformation `X̃_i^{(d)} = (-1)^d X_i^{(d)}` (p. 7). -/
def gradedFlip (x : GPoint) : GPoint :=
  fun v => (-1) ^ (v.1 : ℕ) * x v

/-- Oddness on the graded space: `f(X̃) = -f(X)` almost surely (p. 7). -/
def IsGradedOdd (f : GPoint → ℝ) : Prop :=
  ∀ᵐ x ∂gradedGaussian, f (gradedFlip x) = -f x

/-- An asymptotic Boolean function: `f ∈ L²(X)` with `f ∈ {-1, 1}` almost surely (§3.2, p. 8). -/
def IsAsympBoolean (f : GPoint → ℝ) : Prop :=
  MemLp f 2 gradedGaussian ∧ ∀ᵐ x ∂gradedGaussian, f x = 1 ∨ f x = -1

/-- A distribution `µ` on pairs of odd asymptotic Boolean functions `f, g ∈ L²(X)`, given as a
jointly measurable random pair over a probability space `(Ω, µ)` (Lemma 3.3, p. 8). -/
structure GradedScheme where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  μ : Measure Ω
  [prob : IsProbabilityMeasure μ]
  F : Ω → GPoint → ℝ
  G : Ω → GPoint → ℝ
  measurable_F : Measurable (Function.uncurry F)
  measurable_G : Measurable (Function.uncurry G)
  bool_F : ∀ ω, IsAsympBoolean (F ω)
  bool_G : ∀ ω, IsAsympBoolean (G ω)
  odd_F : ∀ ω, IsGradedOdd (F ω)
  odd_G : ∀ ω, IsGradedOdd (G ω)

attribute [instance] GradedScheme.mΩ GradedScheme.prob

/-- `c_m(µ) = E_{(f,g)∼µ} ⟨Π_m f, Π_m g⟩` on the graded space (§3.2, p. 8). -/
noncomputable def GradedScheme.coeffSeq (S : GradedScheme) (m : ℕ) : ℝ :=
  ∫ ω, gradedInner m (S.F ω) (S.G ω) ∂S.μ

/-- The set `𝒦` of Lemma 3.3 (p. 8): all `c(µ)` for distributions `µ` on pairs of odd asymptotic
Boolean functions on the graded space. -/
def KSet : Set (ℕ → ℝ) :=
  {c | ∃ S : GradedScheme, c = S.coeffSeq}

end GrothendieckPD.Digits


