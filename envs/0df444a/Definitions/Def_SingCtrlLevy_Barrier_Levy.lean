-- Prove2me | Definitions.Def_SingCtrlLevy_Barrier_Levy
-- name    : SingCtrlLevy_Barrier_Levy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:41.182986+00:00
-- url     : https://prove2.me/theorems/623e88ce-f570-4afb-8844-fe28da36ef6d
-- title:
--   §2.1 p. 3, §2.2 p. 4, §4.1 p. 13, §5 p. 21 — Lévy triplet, characteristic exponent Ψ, Lévy process, bounded variation, driftless compound Poisson, Assumptions 2(ii) and 3, Cⁿ_poly, generator L
-- statement:
--   This file fixes the probabilistic model of Noba and Yamazaki's singular control problem: a real Lévy process described by its characteristic triplet.
--
--   1. **Lévy triplet.** A triplet $T=(\gamma,\sigma,\Pi)$ consists of a drift $\gamma\in\mathbb R$, a Gaussian coefficient $\sigma$ and a measure $\Pi$ on $\mathbb R$. It is a *Lévy triplet* if $\sigma\ge 0$, $\Pi(\{0\})=0$ and $\int_{\mathbb R}(1\wedge z^2)\,\Pi(dz)<\infty$.
--   2. **Characteristic exponent.** For $u\in\mathbb R$,
--   $$\Psi(u)=-i\gamma u+\tfrac12\sigma^2u^2+\int_{\mathbb R\setminus\{0\}}\big(1-e^{iuz}+iuz\,1_{\{|z|<1\}}\big)\,\Pi(dz).$$
--   3. **Lévy process with triplet $T$.** A process $X=(X_t)_{t\ge0}$ on a probability space $(\Omega,\mathcal F,\mathbb P)$ is one if every $X_t$ is measurable, $X_0=0$, $X$ has independent and stationary increments ($X_{s+t}-X_s$ has the law of $X_t$), every path is càdlàg, $T$ is a Lévy triplet, and
--   $$\mathbb E\big[e^{iuX_t}\big]=e^{-t\Psi(u)},\qquad t\ge0,\ u\in\mathbb R.$$
--   The law $\mathbb P_x$ of the paper (the process started at $x$) is the law of $x+X$ under $\mathbb P$.
--   4. **Bounded variation.** $X$ has bounded variation paths when $\sigma=0$ and $\int_{(-1,1)}|z|\,\Pi(dz)<\infty$; otherwise it has unbounded variation.
--   5. **Driftless compound Poisson.** $\Psi(u)=\int(1-e^{iuz})\,\Pi(dz)$ with $\Pi$ finite, i.e. $\sigma=0$, $\Pi(\mathbb R)<\infty$ and $\gamma=\int_{(-1,1)}z\,\Pi(dz)$. Assumption 2(i) of the paper is the negation of this.
--   6. **Assumption 2(ii).** There is $\bar\theta>0$ with $\int_{\mathbb R\setminus(-1,1)}e^{\bar\theta|z|}\,\Pi(dz)<\infty$.
--   7. **The classes $C^n_{\mathrm{poly}}$** ($n=1,2$): $n$-times continuously differentiable $g$ with $|g(x)|<b_1|x|^M+b_2$ for some $b_1,b_2>0$, $M\in\mathbb N$.
--   8. **Assumption 3.** If $X$ has unbounded variation, then the running cost $f$ is in $C^2(\mathbb R)$ and $f''$ has polynomial growth: $|f''(x)|\le k_1+k_2|x|^N$.
--   9. **Generator.** For $g:\mathbb R\to\mathbb R$,
--   $$\mathcal Lg(x)=\gamma g'(x)+\tfrac12\sigma^2g''(x)+\int_{\mathbb R\setminus\{0\}}\big(g(x+z)-g(x)-g'(x)z\,1_{\{|z|<1\}}\big)\,\Pi(dz).$$
--
--   These objects carry the paper's standing assumptions on the process and the analytic conditions of its verification step.
--
--   **Formalization Note** Time is $\mathbb R_{\ge0}$. The Lévy measure is a measure on $\mathbb R$ with no atom at $0$. The generator uses Lean's `deriv`; in the bounded-variation case $\sigma=0$, so the second-derivative term vanishes whatever value `deriv (deriv g)` takes. The jump integral of $\mathcal L$ is a Bochner integral; it is a genuine integral for $g\in C^n_{\mathrm{poly}}$ under Assumption 2(ii) (with $n=1$ in the bounded-variation case and $n=2$ otherwise).
-- source:
--   Noba & Yamazaki, On Singular Control for Lévy Processes, arXiv:2008.03021v3, p. 3 §2.1 (Ψ, Lévy measure, bounded variation), p. 4 §2.2 Assumption 2, p. 13 §4.1 (Cⁿ_poly, Assumption 3, generator L), p. 21 §5 (driftless compound Poisson)

import Mathlib

namespace SingCtrlLevy.Barrier

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- A Lévy triplet `(γ, σ, Π)`: drift `γ`, Gaussian coefficient `σ`, Lévy measure `Π`
(Noba–Yamazaki, arXiv:2008.03021v3, §2.1, p. 3). -/
structure Triplet where
  /-- the drift coefficient `γ` -/
  γ : ℝ
  /-- the Gaussian coefficient `σ` -/
  σ : ℝ
  /-- the Lévy measure `Π` -/
  levyMeasure : Measure ℝ

/-- The triplet is admissible: `σ ≥ 0`, `Π{0} = 0` and `∫ (1 ∧ z²) Π(dz) < ∞`. -/
def Triplet.IsLevy (T : Triplet) : Prop :=
  0 ≤ T.σ ∧ T.levyMeasure {0} = 0 ∧
    ∫⁻ z, ENNReal.ofReal (min 1 (z ^ 2)) ∂T.levyMeasure < ⊤

/-- The characteristic exponent (p. 3):
`Ψ(u) = -iγu + σ²u²/2 + ∫ (1 - e^{iuz} + iuz 1{|z|<1}) Π(dz)`, so that
`E[e^{iuX_t}] = e^{-tΨ(u)}`. -/
noncomputable def levyExp (T : Triplet) (u : ℝ) : ℂ :=
  -Complex.I * (T.γ : ℂ) * (u : ℂ) + ((T.σ ^ 2 / 2 * u ^ 2 : ℝ) : ℂ)
    + ∫ z, (1 - Complex.exp (Complex.I * (u : ℂ) * (z : ℂ))
        + Complex.I * (u : ℂ) * (z : ℂ) * ((Set.Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℂ)) z))
        ∂T.levyMeasure

/-- `X = (X_t)_{t ≥ 0}` is a Lévy process started at `0` with triplet `T` on `(Ω, P)`:
every `X_t` is measurable, `X_0 = 0`, independent and stationary increments, càdlàg paths,
`T` is a Lévy triplet, and `E[e^{iuX_t}] = e^{-tΨ(u)}` for all `t ≥ 0`, `u ∈ ℝ`.
The law `P_x` of the paper is the law of `x + X` under `P`. -/
structure IsLevyWith {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (T : Triplet) : Prop where
  measurable : ∀ t, Measurable (X t)
  zero : ∀ ω, X 0 ω = 0
  indepIncrements : HasIndepIncrements X P
  stationaryIncrements : ∀ s t : ℝ≥0,
    IdentDistrib (fun ω => X (s + t) ω - X s ω) (X t) P P
  rightCont : ∀ ω (t : ℝ≥0), ContinuousWithinAt (fun s => X s ω) (Set.Ici t) t
  leftLim : ∀ ω (t : ℝ≥0), 0 < t → ∃ l : ℝ, Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 l)
  triplet : T.IsLevy
  charFun : ∀ (t : ℝ≥0) (u : ℝ),
    ∫ ω, Complex.exp (Complex.I * (u : ℂ) * (X t ω : ℂ)) ∂P
      = Complex.exp (-((t : ℝ) : ℂ) * levyExp T u)

/-- Bounded variation paths (p. 3): `σ = 0` and `∫_{|z|<1} |z| Π(dz) < ∞`. -/
def Triplet.BoundedVariation (T : Triplet) : Prop :=
  T.σ = 0 ∧ ∫⁻ z in Set.Ioo (-1 : ℝ) 1, ENNReal.ofReal |z| ∂T.levyMeasure < ⊤

/-- Driftless compound Poisson (§5, p. 21): `Ψ(u) = ∫ (1 - e^{iuz}) Π(dz)` with `Π` finite,
i.e. `σ = 0`, `Π` finite and `γ = ∫_{(-1,1)} z Π(dz)`. -/
def Triplet.DriftlessCP (T : Triplet) : Prop :=
  T.σ = 0 ∧ IsFiniteMeasure T.levyMeasure ∧
    T.γ = ∫ z in Set.Ioo (-1 : ℝ) 1, z ∂T.levyMeasure

/-- Assumption 2(ii) (p. 4): `∃ θ̄ > 0, ∫_{ℝ∖(-1,1)} e^{θ̄|z|} Π(dz) < ∞`. -/
def Assumption2ii (T : Triplet) : Prop :=
  ∃ θ : ℝ, 0 < θ ∧
    ∫⁻ z in (Set.Ioo (-1 : ℝ) 1)ᶜ, ENNReal.ofReal (Real.exp (θ * |z|)) ∂T.levyMeasure < ⊤

/-- The class `Cⁿ_poly` (p. 13): `n`-times continuously differentiable `g` with
`|g(x)| < b₁|x|^M + b₂` for some `b₁, b₂ > 0`, `M ∈ ℕ`. -/
def CPoly (n : ℕ) (g : ℝ → ℝ) : Prop :=
  ContDiff ℝ n g ∧ ∃ b₁ b₂ : ℝ, 0 < b₁ ∧ 0 < b₂ ∧ ∃ M : ℕ, ∀ x, |g x| < b₁ * |x| ^ M + b₂

/-- Assumption 3 (p. 13): if `X` has unbounded variation, then `f ∈ C²(ℝ)` and `f''` has
polynomial growth. -/
def Assumption3 (T : Triplet) (f : ℝ → ℝ) : Prop :=
  ¬ T.BoundedVariation →
    ContDiff ℝ 2 f ∧ ∃ k₁ k₂ : ℝ, ∃ N : ℕ, ∀ x, |iteratedDeriv 2 f x| ≤ k₁ + k₂ * |x| ^ N

/-- The infinitesimal generator (p. 13):
`Lg(x) = γg'(x) + σ²g''(x)/2 + ∫ (g(x+z) - g(x) - g'(x) z 1{|z|<1}) Π(dz)`. -/
noncomputable def gen (T : Triplet) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  T.γ * deriv g x + T.σ ^ 2 / 2 * deriv (deriv g) x
    + ∫ z, (g (x + z) - g x - deriv g x * z * (Set.Ioo (-1 : ℝ) 1).indicator 1 z) ∂T.levyMeasure

end SingCtrlLevy.Barrier


