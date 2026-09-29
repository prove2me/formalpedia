-- Prove2me | Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
-- name    : AvramDividend_Classical_SpectrallyNegativeLevy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:54:48.982455+00:00
-- url     : https://prove2.me/theorems/933ced80-71c1-4c0f-a6a7-ab7757fc97e9
-- title:
--   Spectrally negative Lévy process with triplet $(c,\sigma,\nu)$, its Laplace exponent, generator and standing assumptions
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb F=(\mathcal F_t)_{t\ge0},P)$ be a filtered probability space, time running over $[0,\infty)$. A **spectrally negative Lévy process** with Lévy triplet $(c,\sigma,\nu)$ is a real process $X=(X_t)_{t\ge0}$ such that
--
--   1. $X_0=0$, every path is right-continuous with left limits, and every path has only downward jumps: $X_t\le X_{t-}$ for all $t>0$;
--   2. $X$ is $\mathbb F$-adapted, and for $s\le t$ the increment $X_t-X_s$ is independent of $\mathcal F_s$ and has the law of $X_{t-s}$;
--   3. $c\in\mathbb R$, $\sigma\ge0$, and $\nu$ is a measure on $\mathbb R$ with $\nu([0,\infty))=0$ and $\int\min(1,y^2)\,\nu(dy)<\infty$;
--   4. for all $t\ge0$ and $\theta\ge0$, $e^{\theta X_t}$ is integrable and $\mathbf E[e^{\theta X_t}]=e^{t\psi(\theta)}$, where the **Laplace exponent** is
--   $$\psi(\theta)=c\theta+\frac{\sigma^2\theta^2}{2}+\int_{(-\infty,0)}\bigl(e^{\theta y}-1-\theta y\,\mathbf 1_{\{|y|<1\}}\bigr)\,\nu(dy).$$
--
--   The file also defines, for such an $X$:
--
--   - **bounded variation**: $\sigma=0$ and $\int_{(-1,0)}|y|\,\nu(dy)<\infty$; the **infinitesimal drift** is then $d=c-\int_{(-1,0)}y\,\nu(dy)$;
--   - **monotone paths**: bounded variation together with $d\le0$ (the negative of a subordinator) or $\nu=0$ (a pure drift);
--   - **condition (3.3)**: $\sigma>0$, or $\int_{(-1,0)}|y|\,\nu(dy)=\infty$, or $\nu$ is absolutely continuous with respect to Lebesgue measure;
--   - the **standing assumptions** of the paper: $X$ does not have monotone paths, $X_1$ is integrable (i.e. $\mathbf E[X_1]>-\infty$), and (3.3) holds;
--   - the **extended generator** acting on $f:\mathbb R\to\mathbb R$,
--   $$\Gamma f(x)=\frac{\sigma^2}{2}f''(x)+cf'(x)+\int_{(-\infty,0)}\bigl[f(x+y)-f(x)-f'(x)y\,\mathbf 1_{\{|y|<1\}}\bigr]\,\nu(dy),$$
--   together with the predicate that the integrand of the jump part is $\nu$-integrable over $(-\infty,0)$ at the point $x$.
--
--   These objects are the model of the classical optimal dividend problem: $X$ is the reserve process of an insurance company before dividends, started from $0$; the process started at $x$ is $x+X$.
--
--   **Formalization Note.** The triplet is recorded explicitly, so that the $c,\sigma,\nu$ of the generator (p. 14) are those of $X$. The law of $X$ is pinned down by the Laplace exponent on $\theta\ge0$ together with independent stationary increments. Independence of increments is required from the past $\sigma$-algebra $\mathcal F_s$, not only from earlier values of $X$, so that strategies adapted to $\mathbb F$ cannot anticipate future increments. The usual conditions on $\mathbb F$ are omitted: they matter only for proofs. Condition (3.3) is printed as $\int_{-1}^0 x\,\nu(dx)=\infty$, which is $\le0$ and cannot hold; the intended clause, $\int_{(-1,0)}|y|\,\nu(dy)=\infty$ (unbounded variation with $\sigma=0$), is formalized. "$\mathbf E_x[X_1]>-\infty$" is formalized as integrability of $X_1$, which is equivalent because $X_1$ has exponential moments of every positive order.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 2 and p. 4 (Section 2), p. 4 (Section 3.1), p. 5 (condition (3.3)), p. 14 (generator Γ)

import Mathlib

/-!
Spectrally negative Lévy process with Lévy triplet `(c, σ, ν)`, its Laplace exponent, its
extended generator, and the standing assumptions of Avram, Palmowski, Pistorius,
*On the optimal dividend problem for a spectrally negative Lévy process*,
arXiv:math/0702893v1, §2 (pp. 2–4), §3.1 (p. 4), (3.3) (p. 5) and the generator on p. 14.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Laplace exponent in Lévy–Khintchine form:
`ψ(θ) = cθ + σ²θ²/2 + ∫_{(-∞,0)} (e^{θy} - 1 - θ y 1_{|y|<1}) ν(dy)`. -/
noncomputable def laplaceExponent (c σ : ℝ) (ν : Measure ℝ) (θ : ℝ) : ℝ :=
  c * θ + σ ^ 2 * θ ^ 2 / 2 +
    ∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂ν

/-- A spectrally negative Lévy process `X = (X_t)_{t ≥ 0}` with Lévy triplet `(c, σ, ν)` on the
filtered probability space `(Ω, 𝓕, P)`, started at `X_0 = 0`. The initial capital `x` is added
explicitly elsewhere (`P_x` is the law of `x + X`). -/
structure SpectrallyNegativeLevy {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) where
  /-- the process -/
  X : ℝ≥0 → Ω → ℝ
  /-- drift coefficient `c` of the triplet (the `c` of the generator, p. 14) -/
  c : ℝ
  /-- Gaussian coefficient `σ ≥ 0` -/
  σ : ℝ
  /-- Lévy measure `ν` -/
  ν : Measure ℝ
  isProbability : IsProbabilityMeasure P
  σ_nonneg : 0 ≤ σ
  /-- no positive jumps: `ν` is carried by `(-∞, 0)` -/
  ν_Ici : ν (Ici 0) = 0
  /-- `∫ min(1, y²) ν(dy) < ∞` -/
  ν_integrable : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν < ⊤
  X_zero : ∀ ω, X 0 ω = 0
  /-- right-continuous paths -/
  rightCont : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Ici t) t
  /-- left limits exist -/
  leftLim : ∀ ω t, 0 < t → ∃ l, Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 l)
  /-- only negative jumps, pathwise: `X_t ≤ X_{t-}` for `t > 0` -/
  noPosJumps : ∀ ω t l, 0 < t → Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 l) → X t ω ≤ l
  adapted : Adapted 𝓕 X
  /-- future increments are independent of the past: `X_t - X_s ⫫ 𝓕_s` for `s ≤ t` -/
  indepIncrements : ∀ s t, s ≤ t →
    Indep (MeasurableSpace.comap (fun ω => X t ω - X s ω) inferInstance) (𝓕 s) P
  /-- stationary increments: `X_t - X_s` has the law of `X_{t-s}` -/
  stationaryIncrements : ∀ s t, s ≤ t →
    IdentDistrib (fun ω => X t ω - X s ω) (X (t - s)) P P
  /-- `E[e^{θ X_t}] = e^{t ψ(θ)}` for `θ ≥ 0` -/
  laplace : ∀ (t : ℝ≥0) (θ : ℝ), 0 ≤ θ →
    Integrable (fun ω => Real.exp (θ * X t ω)) P ∧
      ∫ ω, Real.exp (θ * X t ω) ∂P = Real.exp ((t : ℝ) * laplaceExponent c σ ν θ)

namespace SpectrallyNegativeLevy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- The Laplace exponent `ψ` of `X`. -/
noncomputable def ψ (L : SpectrallyNegativeLevy P 𝓕) : ℝ → ℝ :=
  laplaceExponent L.c L.σ L.ν

/-- `X` has bounded variation: `σ = 0` and `∫_{(-1,0)} |y| ν(dy) < ∞`. -/
def BoundedVariation (L : SpectrallyNegativeLevy P 𝓕) : Prop :=
  L.σ = 0 ∧ ∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂L.ν < ⊤

/-- Infinitesimal drift `d = c - ∫_{(-1,0)} y ν(dy)` (meaningful under bounded variation;
p. 14: `c = d + ∫_{-1}^0 y ν(dy)`). -/
noncomputable def drift (L : SpectrallyNegativeLevy P 𝓕) : ℝ :=
  L.c - ∫ y in Ioo (-1 : ℝ) 0, y ∂L.ν

/-- `X` has monotone paths: bounded variation with nonpositive drift (the negative of a
subordinator), or a pure drift `X_t = c t` (`σ = 0`, `ν = 0`). -/
def HasMonotonePaths (L : SpectrallyNegativeLevy P 𝓕) : Prop :=
  L.BoundedVariation ∧ (L.drift ≤ 0 ∨ L.ν = 0)

/-- Condition (3.3): `σ > 0`, or `∫_{(-1,0)} |y| ν(dy) = ∞`, or `ν ≪ Lebesgue`. -/
def Condition33 (L : SpectrallyNegativeLevy P 𝓕) : Prop :=
  0 < L.σ ∨ ∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂L.ν = ⊤ ∨ L.ν ≪ volume

/-- The paper's standing assumptions for the classical problem: `X` does not have monotone
paths (§2, p. 2), `E[X_1] > -∞` (§2, p. 4; `X_1` is integrable), and (3.3) (p. 5). -/
def Standing (L : SpectrallyNegativeLevy P 𝓕) : Prop :=
  ¬ L.HasMonotonePaths ∧ Integrable (L.X 1) P ∧ L.Condition33

/-- The integrand of the jump part of the generator at `x`:
`y ↦ f(x+y) - f(x) - f'(x) y 1_{|y|<1}`. -/
noncomputable def generatorIntegrand (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  f (x + y) - f x - deriv f x * y * (Ioo (-1 : ℝ) 1).indicator 1 y

/-- The jump integral of the generator at `x` converges (as a Lebesgue integral over
`(-∞, 0)` with respect to `ν`). -/
def GeneratorIntegrable (L : SpectrallyNegativeLevy P 𝓕) (f : ℝ → ℝ) (x : ℝ) : Prop :=
  IntegrableOn (generatorIntegrand f x) (Iio 0) L.ν

/-- The extended generator (p. 14):
`Γf(x) = σ²/2 f''(x) + c f'(x) + ∫_{(-∞,0)} [f(x+y) - f(x) - f'(x) y 1_{|y|<1}] ν(dy)`. -/
noncomputable def generator (L : SpectrallyNegativeLevy P 𝓕) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  L.σ ^ 2 / 2 * iteratedDeriv 2 f x + L.c * deriv f x +
    ∫ y in Iio (0 : ℝ), generatorIntegrand f x y ∂L.ν

end SpectrallyNegativeLevy

end AvramDividend.Classical


