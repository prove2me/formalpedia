-- Prove2me | Definitions.Def_GameRandEnv_FirstOrder_Setting
-- name    : GameRandEnv_FirstOrder_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:00.202019+00:00
-- url     : https://prove2.me/theorems/666c218c-c87e-488b-bd76-5c2799a0dd8b
-- title:
--   §2.1, (2.1), Assumption 2.1, §3.1 — Π, W_p, the linear functional derivative, relative entropy w.r.t. Leb × m, V = F + ηH and the first-order condition (3.1)
-- statement:
--   This file fixes the setting of §2.1 and §3.1 of Conforti, Kazeykina and Ren.
--
--   **Environment and strategies.** Let $\mathbb Y$ be a Polish space with a fixed compatible complete metric and its Borel $\sigma$-algebra, let $\mathsf m$ be a probability measure on $\mathbb Y$, and let $p\ge 1$. Write $\bar{\mathbb R}^d := \mathbb R^d\times\mathbb Y$ and $\bar x=(x,y)$ for its points. The strategy set is
--   $$\Pi := \{\bar\pi \in \mathcal P_p(\bar{\mathbb R}^d) : \bar\pi(\mathbb R^d,\cdot)=\mathsf m\},$$
--   the probability measures on $\bar{\mathbb R}^d$ with $\mathbb Y$-marginal $\mathsf m$ and finite $p$-th moment $\int d(\bar x,\bar x_0)^p\,\bar\pi(d\bar x)<\infty$.
--
--   **Wasserstein distance.** For measures $\mu,\nu$ on $\bar{\mathbb R}^d$,
--   $$\mathcal W_p(\mu,\nu)=\Big(\inf_{\gamma}\int d(\bar x,\bar x')^p\,\gamma(d\bar x,d\bar x')\Big)^{1/p}\in[0,\infty],$$
--   the infimum over couplings $\gamma$ of $\mu$ and $\nu$. A functional $G$ is $\mathcal W_p$-continuous on $\Pi$ if for every $\bar\pi\in\Pi$ and $\varepsilon>0$ there is $\delta>0$ with $|G(\bar\pi')-G(\bar\pi)|<\varepsilon$ whenever $\bar\pi'\in\Pi$ and $\mathcal W_p(\bar\pi,\bar\pi')<\delta$.
--
--   **Linear functional derivative (2.1).** A function $\frac{\delta F}{\delta\bar\pi}:\Pi\times\bar{\mathbb R}^d\to\mathbb R$ is a linear functional derivative of $F:\Pi\to\mathbb R$ if, for all $\nu,\nu'\in\Pi$,
--   $$F(\nu')-F(\nu)=\int_0^1\int_{\bar{\mathbb R}^d}\frac{\delta F}{\delta\bar\pi}\big((1-\lambda)\nu+\lambda\nu',\bar x\big)(\nu'-\nu)(d\bar x)\,d\lambda .$$
--
--   **Assumption 2.1.** $F$ has a linear functional derivative; $F$ is $\mathcal W_p$-continuous on $\Pi$; $\frac{\delta F}{\delta\bar\pi}(\cdot,x,y)$ is $\mathcal W_p$-continuous on $\Pi$ for each $(x,y)$ and $\frac{\delta F}{\delta\bar\pi}(\bar\pi,\cdot,y)$ is continuously differentiable for each $\bar\pi\in\Pi$ and $y$; and $\sup_{\bar\pi\in\Pi}\big|\frac{\delta F}{\delta\bar\pi}(\bar\pi,\bar x)\big|\le C(1+|\bar x|^p)$.
--
--   **Entropy and objective.** For $\bar\pi\ll\mathrm{Leb}\times\mathsf m$ let $\pi(x|y)$ be its density with respect to $\mathrm{Leb}\times\mathsf m$ (equivalently, since the $\mathbb Y$-marginal is $\mathsf m$, the conditional density of $x$ given $y$). The regularizer is the relative entropy
--   $$H(\bar\pi)=H(\bar\pi\,|\,\mathrm{Leb}\times\mathsf m)=\int\ln\pi(x|y)\,\bar\pi(d\bar x)\in(-\infty,+\infty],$$
--   equal to $+\infty$ when $\bar\pi$ is not absolutely continuous. For $\eta>0$, $V(\bar\pi)=F(\bar\pi)+\eta H(\bar\pi)$. $F$ is convex on $\Pi$ if $F((1-t)\nu+t\nu')\le(1-t)F(\nu)+tF(\nu')$ for $\nu,\nu'\in\Pi$ and $t\in[0,1]$.
--
--   **First-order condition (3.1).** $\bar\pi$ satisfies (3.1) if it has a density $\pi(x|y)$ with respect to $\mathrm{Leb}\times\mathsf m$ which, for $\mathsf m$-a.e. $y$, is positive for every $x$, has $x\mapsto\ln\pi(x|y)$ differentiable, and
--   $$\nabla_x\frac{\delta F}{\delta\bar\pi}(\bar\pi,x,y)+\eta\nabla_x\ln\pi(x|y)=0\qquad\text{for all }x .$$
--   Finally $\Xi(\bar x)=\frac{\delta F}{\delta\bar\pi}(\bar\pi,\bar x)+\eta\ln\pi(x|y)$, the function of Step 2 of the proof of Theorem 3.1.
--
--   These objects are shared by the goal theorem and every milestone of the mission.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` and $\bar{\mathbb R}^d$ carries the max product metric; $|\bar x|$ in the growth bound is the distance from $\bar x$ to a base point $(0,y_0)$, with $C$ and $y_0$ chosen once for all $\bar\pi\in\Pi$. $F$ and $\frac{\delta F}{\delta\bar\pi}$ are total functions on measures; only their values on $\Pi$ enter. Two conditions that (2.1) presupposes are made explicit: joint measurability of $\bar x\mapsto\frac{\delta F}{\delta\bar\pi}(\bar\pi,\bar x)$ for $\bar\pi\in\Pi$, and integrability of the $\lambda$-integrand on $[0,1]$. Mixtures use the weights $\max(1-t,0)$ and $\max(t,0)$, which are $1-t$ and $t$ on $[0,1]$. The density is the Radon–Nikodym derivative and $H$ is extended-real valued, set to $+\infty$ also when $\ln\pi(x|y)$ is not $\bar\pi$-integrable (on $\Pi$ its negative part is always integrable, so this only covers the value $+\infty$). In (3.1) the density is an arbitrary measurable version, required to be positive and log-differentiable for $\mathsf m$-a.e. $y$ and every $x$. $\mathcal W_p$ is defined over the metric of $\bar{\mathbb R}^d$ because $\mathbb Y$ is not a normed space.
-- source:
--   Conforti, Kazeykina, Ren, Game on random environment, mean-field Langevin system and neural networks, arXiv:2004.02457v2, pp. 2–4, §2.1, (2.1), Assumption 2.1, Remark 2.2, (1.3), §2.2, Theorem 3.1 (3.1); p. 10, (5.2)

import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal

namespace GameRandEnv.FirstOrder

/-- `ℝ^d`, with Lebesgue measure `volume`. -/
abbrev Rd (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ} {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]

/-- `Π` (§2.1, p. 2): the probability measures `π̄` on `ℝ̄^d = ℝ^d × Y` whose `Y`-marginal is `m`
and which have a finite `p`-th moment. The moment is taken with respect to the product (max) metric
on `ℝ^d × Y` and some base point `z₀`; finiteness does not depend on the base point. -/
def Pi (m : Measure Y) (p : ℝ) : Set (Measure (Rd d × Y)) :=
  {π | IsProbabilityMeasure π ∧ π.map Prod.snd = m ∧
       ∃ z₀ : Rd d × Y, ∫⁻ z, ENNReal.ofReal (dist z z₀ ^ p) ∂π < ∞}

/-- The `p`-Wasserstein distance on measures on `ℝ^d × Y`, with cost `dist ^ p`, valued in `[0, ∞]`:
`W_p(μ, ν) = (inf over couplings γ of μ and ν of ∫ dist(z, z')^p dγ)^{1/p}`. -/
noncomputable def wasserstein (p : ℝ) (μ ν : Measure (Rd d × Y)) : ℝ≥0∞ :=
  (⨅ (γ : Measure ((Rd d × Y) × (Rd d × Y))) (_ : γ.map Prod.fst = μ ∧ γ.map Prod.snd = ν),
      ∫⁻ q, ENNReal.ofReal (dist q.1 q.2 ^ p) ∂γ) ^ (1 / p)

/-- `G : Π → ℝ` is `W_p`-continuous on `Π` (ε–δ form, quantified over `Π` only). -/
def WpContinuousOn (m : Measure Y) (p : ℝ) (G : Measure (Rd d × Y) → ℝ) : Prop :=
  ∀ π ∈ Pi (d := d) m p, ∀ ε > 0, ∃ δ > 0, ∀ π' ∈ Pi (d := d) m p,
    wasserstein p π π' < ENNReal.ofReal δ → |G π' - G π| < ε

/-- The mixture `(1 - t) ν + t ν'`. -/
noncomputable def mix (t : ℝ) (ν ν' : Measure (Rd d × Y)) : Measure (Rd d × Y) :=
  ENNReal.ofReal (1 - t) • ν + ENNReal.ofReal t • ν'

/-- `∫ g d(ν' - ν)`, written as the difference `∫ g dν' - ∫ g dν`. -/
noncomputable def pairDiff (g : Rd d × Y → ℝ) (ν ν' : Measure (Rd d × Y)) : ℝ :=
  ∫ z, g z ∂ν' - ∫ z, g z ∂ν

/-- `δF` is a linear functional derivative of `F` on `Π` ((2.1), p. 2): for every `π̄ ∈ Π` the map
`(x, y) ↦ δF(π̄, x, y)` is measurable, and for all `ν, ν' ∈ Π` the function
`t ↦ ∫ δF((1 - t)ν + tν', ·) d(ν' - ν)` is integrable on `[0, 1]` with
`F(ν') - F(ν) = ∫₀¹ ∫ δF((1 - t)ν + tν', x̄) (ν' - ν)(dx̄) dt`. -/
def IsLinearDerivative (m : Measure Y) (p : ℝ) (F : Measure (Rd d × Y) → ℝ)
    (δF : Measure (Rd d × Y) → Rd d → Y → ℝ) : Prop :=
  (∀ π ∈ Pi (d := d) m p, Measurable (fun z : Rd d × Y => δF π z.1 z.2)) ∧
  ∀ ν ∈ Pi (d := d) m p, ∀ ν' ∈ Pi (d := d) m p,
    IntervalIntegrable (fun t => pairDiff (fun z => δF (mix t ν ν') z.1 z.2) ν ν') volume 0 1 ∧
    F ν' - F ν = ∫ t in (0 : ℝ)..1, pairDiff (fun z => δF (mix t ν ν') z.1 z.2) ν ν'

/-- Assumption 2.1 (pp. 2–3), for the exponent `p ≥ 1` fixed in `Π`: `F ∈ C¹` with linear
functional derivative `δF`; `F` is `W_p`-continuous on `Π`; `δF(·, x, y)` is `W_p`-continuous on `Π`
for every `(x, y)`; `δF(π̄, ·, y)` is continuously differentiable for every `π̄ ∈ Π` and `y`; and
`sup_{π̄ ∈ Π} |δF(π̄, x̄)| ≤ C(1 + |x̄|^p)`, where `|x̄|` is the distance of `x̄ = (x, y)` to `(0, y₀)`. -/
structure Assumption21 (m : Measure Y) (p : ℝ) (F : Measure (Rd d × Y) → ℝ)
    (δF : Measure (Rd d × Y) → Rd d → Y → ℝ) : Prop where
  one_le_p : 1 ≤ p
  linDeriv : IsLinearDerivative m p F δF
  contF : WpContinuousOn (d := d) m p F
  contDeriv : ∀ (x : Rd d) (y : Y), WpContinuousOn (d := d) m p (fun π => δF π x y)
  contDiff : ∀ π ∈ Pi (d := d) m p, ∀ y : Y, ContDiff ℝ 1 (fun x => δF π x y)
  growth : ∃ C : ℝ, ∃ y₀ : Y, ∀ π ∈ Pi (d := d) m p, ∀ (x : Rd d) (y : Y),
    |δF π x y| ≤ C * (1 + dist (x, y) ((0 : Rd d), y₀) ^ p)

/-- `ln π(x|y)`: the logarithm of the density of `π̄` with respect to `Leb × m` (which equals the
conditional density `π(x|y)` because the `Y`-marginal is `m`). Note `Real.log 0 = 0` in Lean. -/
noncomputable def logDens (m : Measure Y) (π : Measure (Rd d × Y)) (z : Rd d × Y) : ℝ :=
  Real.log (π.rnDeriv (volume.prod m) z).toReal

/-- `H(π̄) = H(π̄ | Leb × m) = ∫ ln π(x|y) π̄(dx̄) ∈ (-∞, +∞]`: the relative entropy with respect to
`Leb × m`; it is `+∞` when `π̄` is not absolutely continuous with respect to `Leb × m` or when
`ln π(x|y)` is not `π̄`-integrable. -/
noncomputable def relEnt (m : Measure Y) (π : Measure (Rd d × Y)) : EReal := by
  classical
  exact if π ≪ volume.prod m ∧ Integrable (logDens m π) π
    then ((∫ z, logDens m π z ∂π : ℝ) : EReal) else ⊤

/-- `V(π̄) = F(π̄) + η H(π̄) ∈ (-∞, +∞]`. -/
noncomputable def V (m : Measure Y) (F : Measure (Rd d × Y) → ℝ) (η : ℝ)
    (π : Measure (Rd d × Y)) : EReal :=
  (F π : EReal) + (η : EReal) * relEnt m π

/-- `π̄ ∈ argmin_{π̄' ∈ Π} V(π̄')`. -/
def IsMinimizer (m : Measure Y) (p : ℝ) (F : Measure (Rd d × Y) → ℝ) (η : ℝ)
    (π : Measure (Rd d × Y)) : Prop :=
  π ∈ Pi (d := d) m p ∧ ∀ π' ∈ Pi (d := d) m p, V m F η π ≤ V m F η π'

/-- `F` is convex on `Π` along mixtures: `F((1 - t)ν + tν') ≤ (1 - t)F(ν) + tF(ν')`. -/
def ConvexOnPi (m : Measure Y) (p : ℝ) (F : Measure (Rd d × Y) → ℝ) : Prop :=
  ∀ ν ∈ Pi (d := d) m p, ∀ ν' ∈ Pi (d := d) m p, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    F (mix t ν ν') ≤ (1 - t) * F ν + t * F ν'

/-- The first-order condition (3.1) for `π̄`: `π̄` has a measurable density `ρ` with respect to
`Leb × m` such that, for `m`-a.e. `y` and every `x ∈ ℝ^d`, `ρ(x, y) > 0`, `x ↦ ln ρ(x, y)` is
differentiable at `x`, and `∇ₓ δF(π̄, x, y) + η ∇ₓ ln ρ(x, y) = 0`. -/
def FirstOrderCondition (m : Measure Y) (δF : Measure (Rd d × Y) → Rd d → Y → ℝ) (η : ℝ)
    (π : Measure (Rd d × Y)) : Prop :=
  ∃ ρ : Rd d × Y → ℝ, Measurable ρ ∧
    π = (volume.prod m).withDensity (fun z => ENNReal.ofReal (ρ z)) ∧
    ∀ᵐ y ∂m, ∀ x : Rd d, 0 < ρ (x, y) ∧
      DifferentiableAt ℝ (fun x' => Real.log (ρ (x', y))) x ∧
      gradient (fun x' => δF π x' y) x + η • gradient (fun x' => Real.log (ρ (x', y))) x = 0

/-- `Ξ(x̄) = δF(π̄, x̄) + η ln π(x|y)` (§5.1, Step 2, (5.2)). -/
noncomputable def Xi (m : Measure Y) (δF : Measure (Rd d × Y) → Rd d → Y → ℝ) (η : ℝ)
    (π : Measure (Rd d × Y)) (z : Rd d × Y) : ℝ :=
  δF π z.1 z.2 + η * logDens m π z

end GameRandEnv.FirstOrder


