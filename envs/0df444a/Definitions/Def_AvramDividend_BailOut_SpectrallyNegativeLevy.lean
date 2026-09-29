-- Prove2me | Definitions.Def_AvramDividend_BailOut_SpectrallyNegativeLevy
-- name    : AvramDividend_BailOut_SpectrallyNegativeLevy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:01:12.359162+00:00
-- url     : https://prove2.me/theorems/86405435-3279-43d6-8c80-6a7174398258
-- title:
--   Spectrally negative Lévy process with triplet $(c,\sigma,\nu)$ on a filtered probability space
-- statement:
--   A **Lévy triplet without positive jumps** is a triple $(c,\sigma,\nu)$ with $c\in\mathbb R$, a Gaussian coefficient $\sigma\ge 0$ and a Lévy measure $\nu$ on $\mathbb R$ carried by $(-\infty,0)$ with $\int \min(1,y^2)\,\nu(dy)<\infty$. Its **Laplace exponent** is
--
--   $$\psi(\theta)=c\theta+\frac{\sigma^2}{2}\theta^2+\int_{(-\infty,0)}\bigl(e^{\theta y}-1-\theta y\,\mathbf 1_{\{|y|<1\}}\bigr)\,\nu(dy),\qquad \theta\ge 0 .$$
--
--   The triplet has **bounded variation** if $\sigma=0$ and $\int_{(-1,0)}|y|\,\nu(dy)<\infty$; its **drift** is then $d=c-\int_{(-1,0)}y\,\nu(dy)$, and the process is $X_t=dt-S_t$ with $S$ a subordinator. The paths are **monotone** exactly when $\sigma=0$ and $\nu=0$, or the triplet has bounded variation with $d\le 0$. **Condition (3.3)** is: $\sigma>0$, or $\int_{(-1,0)}|y|\,\nu(dy)=\infty$, or $\nu$ is absolutely continuous with respect to Lebesgue measure.
--
--   A **spectrally negative Lévy process** on a filtered probability space $(\Omega,\mathcal F,\mathbb F=\{\mathcal F_t\}_{t\ge0},P)$ is a process $X=\{X_t\}_{t\ge 0}$ together with a triplet $(c,\sigma,\nu)$ such that:
--
--   1. $X_0=0$ and every path is right-continuous with left limits;
--   2. $X$ is $\mathbb F$-adapted, and for $s\le t$ the increment $X_t-X_s$ is independent of $\mathcal F_s$ and has the law of $X_{t-s}$;
--   3. $E[e^{\theta X_t}]=e^{t\psi(\theta)}$ for all $t\ge0$ and $\theta\ge 0$;
--   4. the filtration satisfies the usual conditions: it is right-continuous and $\mathcal F_0$ contains every $P$-null set.
--
--   The law $P_x$ of the paper (the process started at $x$) is the law of $x+X$ under $P$. Write $\psi'(0+)=E[X_1]$.
--
--   The **standing assumptions** of the paper are: $X$ does not have monotone paths (p. 2), condition (3.3) holds (p. 5), and $E[X_1]>-\infty$, i.e. $X_1$ is integrable (p. 4).
--
--   This is the process model on which every statement of the mission is built.
--
--   **Formalization Note** Time is indexed by $\mathbb R_{\ge 0}$. Independence of increments is required from the past $\sigma$-algebra $\mathcal F_s$, not only from earlier increments, because controls are $\mathbb F$-adapted. The paper prints the middle clause of (3.3) as $\int_{-1}^0 x\,\nu(dx)=\infty$; it is formalized as $\int_{(-1,0)}|y|\,\nu(dy)=\infty$ (unbounded variation without Gaussian part). Since $X$ has no positive jumps, $E[X_1^+]<\infty$ always, so $E[X_1]>-\infty$ is integrability of $X_1$, and $\psi'(0+)$ is defined as $E[X_1]$ (p. 12 uses $E_0[X_{\eta(q)}]=\psi'(0+)/q$).
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 2 (Section 2), p. 4 (standing assumptions, Section 3.1), p. 5 (condition (3.3)), p. 14 (triplet of the generator)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace AvramDividend.BailOut

/-- A Lévy triplet `(c, σ, ν)` without positive jumps: drift parameter `c`, Gaussian
coefficient `σ ≥ 0`, and a Lévy measure `ν` carried by `(-∞, 0)` with
`∫ min(1, y²) ν(dy) < ∞`. -/
structure LevyTriplet where
  c : ℝ
  σ : ℝ
  ν : Measure ℝ
  σ_nonneg : 0 ≤ σ
  ν_nonneg_support : ν (Set.Ici 0) = 0
  ν_levy : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν < ∞

namespace LevyTriplet

/-- The Laplace exponent `ψ(θ) = cθ + σ²θ²/2 + ∫_{(-∞,0)} (e^{θy} - 1 - θy 1_{|y|<1}) ν(dy)`
(for `θ ≥ 0`; the paper's `ψ`, p. 4, written with the triplet of the generator `Γ`, p. 14). -/
noncomputable def laplaceExponent (T : LevyTriplet) (θ : ℝ) : ℝ :=
  T.c * θ + T.σ ^ 2 * θ ^ 2 / 2 +
    ∫ y, (Real.exp (θ * y) - 1 - (if |y| < 1 then θ * y else 0)) ∂T.ν

/-- Bounded variation: no Gaussian part and `∫_{(-1,0)} |y| ν(dy) < ∞`. -/
def BoundedVariation (T : LevyTriplet) : Prop :=
  T.σ = 0 ∧ ∫⁻ y in Set.Ioo (-1 : ℝ) 0, ‖y‖ₑ ∂T.ν < ∞

/-- The infinitesimal drift `d = c - ∫_{(-1,0)} y ν(dy)` of a bounded-variation triplet
(so that `X_t = d t - S_t` with `S` a subordinator; p. 5 and p. 14). -/
noncomputable def drift (T : LevyTriplet) : ℝ :=
  T.c - ∫ y in Set.Ioo (-1 : ℝ) 0, y ∂T.ν

/-- The paths are monotone exactly when the process is a pure drift (`σ = 0`, `ν = 0`) or has
bounded variation with nonpositive drift `d ≤ 0` (then `X = d t - S_t` is nonincreasing). -/
def MonotonePaths (T : LevyTriplet) : Prop :=
  (T.σ = 0 ∧ T.ν = 0) ∨ (T.BoundedVariation ∧ T.drift ≤ 0)

/-- Standing condition (3.3), p. 5: `σ > 0`, or `∫_{(-1,0)} |y| ν(dy) = ∞` (unbounded
variation without Gaussian part; the paper prints `∫_{-1}^0 x ν(dx) = ∞`), or `ν ≪ Lebesgue`. -/
def Condition33 (T : LevyTriplet) : Prop :=
  0 < T.σ ∨ ∫⁻ y in Set.Ioo (-1 : ℝ) 0, ‖y‖ₑ ∂T.ν = ∞ ∨ T.ν ≪ volume

end LevyTriplet

/-- A spectrally negative Lévy process `X = {X_t, t ≥ 0}` with triplet `(c, σ, ν)`, started at
`X_0 = 0`, on a filtered probability space `(Ω, F, 𝔽, P)` whose filtration satisfies the usual
conditions (right-continuous and containing the `P`-null sets): càdlàg paths, adapted to `𝔽`,
increments `X_t - X_s` independent of `𝓕_s` and stationary, and
`E[e^{θ X_t}] = e^{t ψ(θ)}` for all `θ ≥ 0`. The law `P_x` of the paper is the law of `x + X`. -/
structure SpectrallyNegativeLevy {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) where
  triplet : LevyTriplet
  X : ℝ≥0 → Ω → ℝ
  X_zero : ∀ ω, X 0 ω = 0
  right_continuous : ∀ ω (t : ℝ≥0), ContinuousWithinAt (fun s => X s ω) (Set.Ici t) t
  left_limits : ∀ ω (t : ℝ≥0), 0 < t → ∃ l : ℝ, Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 l)
  adapted : Adapted 𝓕 X
  indep_increments : ∀ s t : ℝ≥0, s ≤ t →
    Indep (MeasurableSpace.comap (fun ω => X t ω - X s ω) inferInstance) (𝓕 s) P
  stationary_increments : ∀ s t : ℝ≥0, s ≤ t →
    P.map (fun ω => X t ω - X s ω) = P.map (X (t - s))
  laplace : ∀ (t : ℝ≥0) (θ : ℝ), 0 ≤ θ →
    ∫ ω, Real.exp (θ * X t ω) ∂P = Real.exp (t * triplet.laplaceExponent θ)
  filtration_right_continuous : 𝓕.IsRightContinuous
  filtration_complete : ∀ s : Set Ω, P s = 0 → MeasurableSet[𝓕 0] s

namespace SpectrallyNegativeLevy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- `ψ'(0+) = E[X_1]` (p. 12: `E_0[X_{η(q)}] = ψ'(0+)/q`). It is finite exactly when
`X_1` is integrable, which is the standing assumption `E_x[X_1] > -∞` of p. 4. -/
noncomputable def psiDerivZero (L : SpectrallyNegativeLevy P 𝓕) : ℝ :=
  ∫ ω, L.X 1 ω ∂P

/-- The standing assumptions of the paper on the process: `X` does not have monotone paths
(p. 2), condition (3.3) holds (p. 5), and `E[X_1] > -∞`, i.e. `X_1 ∈ L¹(P)` (p. 4). -/
def StandingAssumptions (L : SpectrallyNegativeLevy P 𝓕) : Prop :=
  ¬ L.triplet.MonotonePaths ∧ L.triplet.Condition33 ∧ Integrable (L.X 1) P

end SpectrallyNegativeLevy

end AvramDividend.BailOut


