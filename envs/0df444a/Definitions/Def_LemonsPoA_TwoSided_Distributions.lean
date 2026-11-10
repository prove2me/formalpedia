-- Prove2me | Definitions.Def_LemonsPoA_TwoSided_Distributions
-- name    : LemonsPoA_TwoSided_Distributions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:10:48.470822+00:00
-- url     : https://prove2.me/theorems/6584c610-8c8d-4f97-97d9-1c74a77e059e
-- title:
--   Convex order against an exponential, log-concave densities (joint, marginal, with constant coordinates), correlation, monotone hazard rate
-- statement:
--   Distributional notions used by the regularity conditions and the lemmas of §4.
--
--   * **Convex order against an exponential** (Definition 5.2 item 1). A law $\nu$ on $\mathbb R$ is dominated in convex order by an exponential variable $Z$ of mean $\mu$ if $E[\varphi(C)]\le E[\varphi(Z)]$ for every convex $\varphi:\mathbb R\to\mathbb R$, where $C\sim\nu$.
--   * **Log-concave density.** $\nu$ has a Lebesgue density $f$ that is log-concave: $f\ge 0$ and $f(a)^s f(b)^{1-s}\le f(sa+(1-s)b)$ for $s\in[0,1]$. `LogConcaveOrConst`: a log-concave density or a point mass.
--   * **Log-concave preferences** (Definition 5.2 item 4 with Definition 1.4 item 1). Under $\theta\sim G$: $(x(\theta),y(\theta))$ has a log-concave density on $\mathbb R^2$; or one coordinate is a.s. constant and the other has a log-concave density on $\mathbb R$.
--   * **Correlation** $\mathrm{Corr}(x,y)=\mathrm{Cov}(x,y)/(\sqrt{\mathrm{Var}\,x}\sqrt{\mathrm{Var}\,y})$ under $G$.
--   * **Monotone hazard rate.** $\nu$ has a density $f$ whose hazard rate $h(t)=f(t)/\Pr[T>t]$ is nondecreasing on $\{t\ge 0:\Pr[T>t]>0\}$.
--
--   **Formalization Note** The exponential law of mean $\mu$ is Mathlib's `expMeasure μ⁻¹` (rate $\mu^{-1}$). `CxLeExp ν μ` quantifies over convex $\varphi$ with $\varphi(Z)$ integrable and asserts $\varphi(C)$ integrable and the inequality of Bochner integrals; for convex $\varphi$ both expectations lie in $(-\infty,+\infty]$ and the inequality is trivial when $E[\varphi(Z)]=+\infty$, so this is the paper's condition. Log-concavity is the published `ConvexOptimization.LogConcaveOn` on `Set.univ` (power form, zeros allowed) and densities are with respect to Lebesgue measure (`volume.withDensity`). "Constant" means $G$-a.s. constant. `corr` is the plain quotient, so it is $0$ when a coordinate has zero variance; with a constant coordinate the condition $\mathrm{Corr}\ge\rho$ therefore reads $\rho\le 0$, matching the paper's "take this to be satisfied for $\rho=0$". The MHR density is existential: some version $f$ of the density has a nondecreasing hazard rate.
-- source:
--   Durvasula, Roughgarden, The Price of Anarchy in Markets for Lemons, STOC 2027 submission (manuscript sha256 5a158b50…), pp. 9-10, 22-23, 27-28, Definition 1.4, Definition 5.2 items 1, 4, 5, Theorem 4.5

import Mathlib
import Definitions.Def_LogConcaveOn

open MeasureTheory ProbabilityTheory

namespace LemonsPoA.TwoSided

/-- Convex-order domination by an exponential (Definition 5.2, item 1; display (10)): for every
convex `φ : ℝ → ℝ`, `E[φ(C)] ≤ E[φ(Z)]` where `C ∼ ν` and `Z` is exponential with mean `µ`
(rate `µ⁻¹`). Stated for every convex `φ` with `φ(Z)` integrable, requiring `φ(C)` integrable and
the inequality of Bochner integrals (when `E[φ(Z)] = +∞` the source inequality is trivial). -/
def CxLeExp (ν : Measure ℝ) (μ : ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ → Integrable φ (expMeasure μ⁻¹) →
    Integrable φ ν ∧ ∫ t, φ t ∂ν ≤ ∫ t, φ t ∂(expMeasure μ⁻¹)

/-- The law `ν` on `ℝ` has a log-concave Lebesgue density `f` (log-concavity in the power form
of the published `ConvexOptimization.LogConcaveOn`, zero values allowed). -/
def HasLogConcaveDensity (ν : Measure ℝ) : Prop :=
  ∃ f : ℝ → ℝ, Measurable f ∧ ConvexOptimization.LogConcaveOn Set.univ f ∧
    ν = volume.withDensity (fun t => ENNReal.ofReal (f t))

/-- `ν` has a log-concave density, or is the law of a constant. -/
def LogConcaveOrConst (ν : Measure ℝ) : Prop :=
  HasLogConcaveDensity ν ∨ ∃ z₀ : ℝ, ν = Measure.dirac z₀

/-- Under `G`, `(x(θ), y(θ))` has a log-concave Lebesgue density on `ℝ × ℝ`. -/
def HasLogConcaveJointDensity {Θ : Type*} [MeasurableSpace Θ] (G : Measure Θ) (x y : Θ → ℝ) :
    Prop :=
  ∃ f : ℝ × ℝ → ℝ, Measurable f ∧ ConvexOptimization.LogConcaveOn Set.univ f ∧
    G.map (fun θ => (x θ, y θ)) = volume.withDensity (fun p => ENNReal.ofReal (f p))

/-- The log-concavity condition on preferences (Definition 5.2 item 4, read with the
constant-coordinate clause of Definition 1.4 item 1): `(x, y)` has a joint log-concave density
under `G`; or `x` is `G`-a.s. constant and `y` has a log-concave density; or `y` is `G`-a.s.
constant and `x` has a log-concave density. -/
def LogConcavePrefs {Θ : Type*} [MeasurableSpace Θ] (G : Measure Θ) (x y : Θ → ℝ) : Prop :=
  HasLogConcaveJointDensity G x y ∨
    ((∃ x₀ : ℝ, ∀ᵐ θ ∂G, x θ = x₀) ∧ HasLogConcaveDensity (G.map y)) ∨
    ((∃ y₀ : ℝ, ∀ᵐ θ ∂G, y θ = y₀) ∧ HasLogConcaveDensity (G.map x))

/-- Correlation `Corr(x, y) = Cov(x, y) / (√Var x √Var y)` under `G` (plain quotient: it is
`0` when a coordinate has zero variance). -/
noncomputable def corr {Θ : Type*} [MeasurableSpace Θ] (G : Measure Θ) (x y : Θ → ℝ) : ℝ :=
  covariance x y G / (Real.sqrt (variance x G) * Real.sqrt (variance y G))

/-- `ν` has a Lebesgue density `f` with nondecreasing hazard rate
`h(t) = f(t) / Pr[T > t]` on `{t ≥ 0 : Pr[T > t] > 0}` (monotone hazard rate, MHR). -/
def HasMHRDensity (ν : Measure ℝ) : Prop :=
  ∃ f : ℝ → ℝ, Measurable f ∧ (∀ t, 0 ≤ f t) ∧
    ν = volume.withDensity (fun t => ENNReal.ofReal (f t)) ∧
    MonotoneOn (fun t => f t / (ν (Set.Ioi t)).toReal) {t | 0 ≤ t ∧ 0 < (ν (Set.Ioi t)).toReal}

end LemonsPoA.TwoSided


