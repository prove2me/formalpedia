-- Prove2me | Definitions.Def_MeanFieldContest_Model
-- name    : MeanFieldContest_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:53:13.189537+00:00
-- url     : https://prove2.me/theorems/3154283f-0ac3-4eef-b4c1-6cb34d067b7d
-- title:
--   The mean field contest: rewards, $g^{-1}$, $\bar\mu_\infty$, scale function, feasible laws, payoff (2.1), equilibrium, value function, $u^*$, $F^*$
-- statement:
--   The objects of the stopping contest of Nutz and Zhang.
--
--   1. **Reward function.** $R:[0,1]\to\mathbb R_+$ decreasing (non-strictly), right-continuous, with $R(0)>R(1-)=R(1)$. Write $g(y):=R(1-y)$, $\bar R:=\int_0^1R(r)\,dr$, and
--   $$\bar\mu_\infty:=\frac{\sigma^2}{2x_0}\log\frac{R(0)-R(1)}{R(0)-\bar R}.$$
--   2. **Inverse of $g$.** $g^{-1}(z)=1\wedge\inf\{y\in[0,1]:g(y)>z\}$ for real $z$; on $[R(1),R(0))$ this is the infimum, and $g^{-1}(R(0))=1$.
--   3. **Scale function** (2.2). $h(x)=\dfrac{e^{-2\mu x/\sigma^2}-1}{e^{-2\mu x_0/\sigma^2}-1}$ if $\mu\ne0$ and $h(x)=x/x_0$ if $\mu=0$, so $h(x_0)=1$.
--   4. **Feasible laws.** For a start $x$, a law $\nu$ is feasible if on some probability space there are a filtration $\mathbb G$, a $\mathbb G$-Brownian motion $W$ and a finite $\mathbb G$-stopping time $\tau$ with $\nu$ the law of $X_{\tau\wedge T_0}$, where $X_t=x+\mu t+\sigma W_t$ and $T_0=\inf\{t\ge0:X_t\le0\}$. For $x=x_0$ this is the paper's set $\mathcal F$.
--   5. **Payoff** (2.1). If the others use $F$, stopping at $x$ pays $\xi^F(x)=g(F(x))$ when $F(x)=F(x-)$, and otherwise the tie-splitting average
--   $$\xi^F(x)=\frac1{F(x)-F(x-)}\int_{F(x-)}^{F(x)}g(y)\,dy.$$
--   6. **Equilibrium.** $F\in\mathcal F$ with $\int\xi^F\,dF\ge\int\xi^F\,d\tilde F$ for all $\tilde F\in\mathcal F$.
--   7. **Value function.** $u^F(x)$ is the supremum of $\int\xi^F\,dG$ over the laws $G$ feasible from $x$.
--   8. **Closed forms** of Theorem 2.2. $u^*(x)=[R(1)+(\bar R-R(1))h(x)]\wedge R(0)$, and $F^*(x)=g^{-1}(u^*(x))$ for $x\ge0$, $F^*(x)=0$ for $x<0$.
--
--   These objects state the whole mission. The feasible set and the value function are the stochastic objects of the paper; their analytic descriptions are theorems of the mission.
--
--   **Formalization Note** $R$ is a function on $\mathbb R$ read only on $[0,1]$. A randomized stopping time is a stopping time of a filtration larger than that of $W$. The sample space ranges over `Type`. The position is required to be a.e.-measurable, since `Measure.map` of a non-measurable map is the zero measure.
-- source:
--   Nutz–Zhang, Mean Field Contest with Singularity, arXiv:2103.04219v1, §2, pp.4–5: reward function p.4; model p.4; g, (2.1), (2.2), equilibrium, value function, R̄, µ̄∞, g⁻¹, Theorem 2.2 p.5; extension of g⁻¹ in the proof of Theorem 4.1, p.18

import Mathlib
import Definitions.Def_EllsbergLearning_IsBrownianWrt

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

namespace MeanFieldContest

/-- **Reward function.** Nutz–Zhang, *Mean Field Contest with Singularity*, arXiv:2103.04219v1,
§2, p.4: "a right-continuous and decreasing function `R : [0,1] → ℝ₊` satisfying
`R(0) > R(1−) = R(1)`".

**Formalization Note.** `R : ℝ → ℝ`, and every condition is on `[0,1]`: no object of this file
reads `R` outside `[0,1]`. "Decreasing" is non-strict (footnote 1, p.4). The printed
`R(0) > R(1−) = R(1)` is the two fields `tendsto_one` and `gap` together. Right-continuity at `1`
is void, so it is required on `[0,1)`. -/
structure IsRewardFunction (R : ℝ → ℝ) : Prop where
  antitone : AntitoneOn R (Icc 0 1)
  nonneg : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ R r
  rightCont : ∀ r ∈ Ico (0 : ℝ) 1, ContinuousWithinAt R (Ici r) r
  tendsto_one : Tendsto R (𝓝[<] 1) (𝓝 (R 1))
  gap : R 1 < R 0

/-- `g(y) := R(1 − y)`, arXiv:2103.04219v1, §2, p.5. -/
def g (R : ℝ → ℝ) (y : ℝ) : ℝ := R (1 - y)

/-- The average reward `R̄ = ∫₀¹ R(r) dr`, arXiv:2103.04219v1, §2, p.5.

**Formalization Note.** `R` is monotone on `[0,1]`, hence interval integrable there, so the
integral has no junk value for any reward considered in this mission. -/
noncomputable def Rbar (R : ℝ → ℝ) : ℝ := ∫ r in (0 : ℝ)..1, R r

/-- The critical drift `µ̄∞ := σ²/(2x₀) · log((R(0) − R(1))/(R(0) − R̄))`,
arXiv:2103.04219v1, §2, p.5.

**Formalization Note.** For a reward function, `R(1) < R̄ < R(0)` (the first by right-continuity
at `0`, the second by `R(1−) < R(0)`), so the argument of the logarithm exceeds `1`. -/
noncomputable def muBarInfty (R : ℝ → ℝ) (x₀ σ : ℝ) : ℝ :=
  σ ^ 2 / (2 * x₀) * Real.log ((R 0 - R 1) / (R 0 - Rbar R))

open Classical in
/-- The right-continuous inverse `g⁻¹` of `g`, arXiv:2103.04219v1, §2, p.5:
`g⁻¹(z) = inf{y ∈ [0,1] : g(y) > z}` for `z ∈ [R(1), R(0))`, `g⁻¹(R(0)) := 1`.

**Formalization Note.** Defined for every real `z` by the paper's own extension
`g⁻¹(z) = 1 ∧ inf{y : g(y) > z}` (proof of Theorem 4.1, p.18), which Lemma 3.8 needs because it
applies `g⁻¹` to values of a majorant `φ`. For `z < R 0` the set contains `y = 1`, so the `sInf` is
never of the empty set; for `z ≥ R 0` the value is `1`. -/
noncomputable def gInv (R : ℝ → ℝ) (z : ℝ) : ℝ :=
  if z < R 0 then sInf {y | y ∈ Icc (0 : ℝ) 1 ∧ z < g R y} else 1

open Classical in
/-- The scale function (2.2), arXiv:2103.04219v1, Lemma 2.1, p.5, normalized by `h(x₀) = 1`:
`h(x) = (exp(−2µx/σ²) − 1)/(exp(−2µx₀/σ²) − 1)` if `µ ≠ 0`, and `h(x) = x/x₀` if `µ = 0`.
The player's starting level may differ from `x₀`; `h` stays normalized at `x₀` throughout. -/
noncomputable def scale (x₀ μ σ x : ℝ) : ℝ :=
  if μ = 0 then x / x₀
  else (Real.exp (-2 * μ * x / σ ^ 2) - 1) / (Real.exp (-2 * μ * x₀ / σ ^ 2) - 1)

/-- The drifted Brownian motion `X_t = x + µt + σW_t` before absorption,
arXiv:2103.04219v1, §2, p.4. -/
def driftedPath {Ω : Type*} (x μ σ : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  x + μ * (t : ℝ) + σ * W t ω

/-- The absorption time `T₀ := inf{t ≥ 0 : X_t ≤ 0}`, with value `⊤` if the path never reaches
`(−∞, 0]`. -/
noncomputable def absorptionTime {Ω : Type*} (x μ σ : ℝ) (W : ℝ≥0 → Ω → ℝ) : Ω → WithTop ℝ≥0 :=
  hittingAfter (driftedPath x μ σ W) (Iic 0) 0

/-- The stopping position `Y = X_{τ ∧ T₀}` of the process absorbed at `0` and stopped at `τ`,
arXiv:2103.04219v1, §2, p.4: "a drifted Brownian motion … with absorption at `x = 0`", "Let
`Yⁱ = Xⁱ_{τⁱ}` be the position at stopping". -/
noncomputable def stoppingPosition {Ω : Type*} (x μ σ : ℝ) (W : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) : Ω → ℝ :=
  stoppedValue (driftedPath x μ σ W) (fun ω => min (τ ω) (absorptionTime x μ σ W ω))

/-- **The feasible laws.** arXiv:2103.04219v1, §2, pp.4–5: the set `𝓕` "of distributions that are
feasible, i.e., can be attained by stopping `Xⁱ` with a randomized stopping time", for a player
started at `x`. `ν` is feasible iff on some probability space there are a filtration `𝔾`, a
`𝔾`-Brownian motion `W` and a `𝔾`-stopping time `τ < ∞` a.s. such that `ν` is the law of the position
`X_{τ ∧ T₀}` of the absorbed process.

**Formalization Note.** A randomized stopping time is a stopping time of a filtration larger than
that of `W`, with `W` still a `𝔾`-Brownian motion. `Ω` ranges over `Type`. The position must be
a.e.-measurable, because `Measure.map` of a non-a.e.-measurable map is `0`. This is the stochastic
definition of the paper's set; its characterization by the scale function is Lemma 2.1, a theorem. -/
def feasibleLaws (x μ σ : ℝ) : Set (Measure ℝ) :=
  {ν | ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (𝔾 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0),
      IsProbabilityMeasure P ∧ EllsbergLearning.IsBrownianWrt 𝔾 P W ∧ IsStoppingTime 𝔾 τ ∧
      (∀ᵐ ω ∂P, τ ω < ⊤) ∧ AEMeasurable (stoppingPosition x μ σ W τ) P ∧
      P.map (stoppingPosition x μ σ W τ) = ν}

open Classical in
/-- The payoff (2.1), arXiv:2103.04219v1, §2, p.5: the reward for stopping at `x` if all other
players use `F`: `ξ^F(x) = g(F(x))` if `F(x) = F(x−)`, and
`ξ^F(x) = (F(x) − F(x−))⁻¹ ∫_{F(x−)}^{F(x)} g(y) dy` if `F(x) > F(x−)`.

**Formalization Note.** `F(x) = cdf F x` and `F(x−) = F.real (Iio x)`. -/
noncomputable def xi (R : ℝ → ℝ) (F : Measure ℝ) (x : ℝ) : ℝ :=
  if cdf F x = F.real (Iio x) then g R (cdf F x)
  else (cdf F x - F.real (Iio x))⁻¹ * ∫ y in (F.real (Iio x))..(cdf F x), g R y

/-- **Mean field equilibrium.** arXiv:2103.04219v1, §2, p.5: "`F ∈ 𝓕` is a mean field equilibrium if
no player is incentivized to deviate from `F`; that is, `∫ξ^F dF ≥ ∫ξ^F dF̃` for all `F̃ ∈ 𝓕`."

**Formalization Note.** `ξ^F` is monotone with values between `g(0)` and `g(1)`, hence integrable
against every probability measure, so neither Bochner integral has a junk value. -/
def IsMFE (x₀ μ σ : ℝ) (R : ℝ → ℝ) (F : Measure ℝ) : Prop :=
  F ∈ feasibleLaws x₀ μ σ ∧
    ∀ G ∈ feasibleLaws x₀ μ σ, ∫ x, xi R F x ∂G ≤ ∫ x, xi R F x ∂F

/-- **Value function.** arXiv:2103.04219v1, §2, p.5: `u(x)` is "the supremum expected reward
achievable for a player starting at level `x` (instead of `x₀`) if all others use `F`".

**Formalization Note.** A supremum over reachable laws, not the concave envelope (that identity is a
milestone). The set is nonempty and bounded above by `g(1)` for `x ≥ 0`, so the real `sSup` is
genuine there. -/
noncomputable def valueFn (μ σ : ℝ) (R : ℝ → ℝ) (F : Measure ℝ) (x : ℝ) : ℝ :=
  sSup {v | ∃ G ∈ feasibleLaws x μ σ, v = ∫ y, xi R F y ∂G}

/-- The closed-form value `u*(x) = [R(1) + (R̄ − R(1))h(x)] ∧ R(0)`,
arXiv:2103.04219v1, Theorem 2.2, p.5. -/
noncomputable def uStar (x₀ μ σ : ℝ) (R : ℝ → ℝ) (x : ℝ) : ℝ :=
  min (R 1 + (Rbar R - R 1) * scale x₀ μ σ x) (R 0)

open Classical in
/-- The closed-form cdf (2.3), `F*(x) = g⁻¹([R(1) + (R̄ − R(1))h(x)] ∧ R(0))`,
arXiv:2103.04219v1, Theorem 2.2, p.5.

**Formalization Note.** `F*` is a distribution on `[0,∞)`, so `F*(x) := 0` for `x < 0`. -/
noncomputable def FStar (x₀ μ σ : ℝ) (R : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 ≤ x then gInv R (uStar x₀ μ σ R x) else 0

end MeanFieldContest


