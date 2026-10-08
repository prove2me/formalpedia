-- Prove2me | Definitions.Def_TSTutorial_InfoRatio_Setting
-- name    : TSTutorial_InfoRatio_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:44.763219+00:00
-- url     : https://prove2.me/theorems/f1155908-f447-4f9e-bff7-43f9fbc51b83
-- title:
--   §4 and §8.1.2, pp. 18–19, 70–71, 75–76 — the Bayesian online decision problem, algorithms, Bayesian regret, (8.7) and H(x*)
-- statement:
--   This file sets up the general online decision problem of §4 and §8.1.2 of the tutorial, together with the information quantities of its information-theoretic regret analysis.
--
--   **The model.** An agent repeatedly selects an action $x_t$ from a finite set $\mathcal X$ and observes an outcome $y_t$ in a finite set $\mathcal Y$. An unknown parameter $\theta$ takes values in a measurable space $\Theta$ and has a prior probability distribution $P$. Given $\theta$ and the action $x$, the outcome is drawn from the conditional distribution $q_\theta(\cdot\mid x)$: the numbers $q_\theta(y\mid x)$ are nonnegative, sum to $1$ over $y$, and depend measurably on $\theta$. The agent receives the reward $r(y_t)$ for a known function $r:\mathcal Y\to\mathbb R$. The mean reward of action $x$ under $\theta$ is
--   $$\mu(x,\theta)=\sum_{y\in\mathcal Y} q_\theta(y\mid x)\,r(y),$$
--   and the optimal action is $x^*=x^*(\theta)\in\arg\max_{x\in\mathcal X}\mu(x,\theta)$, given by a fixed selector whose level sets $\{\theta : x^*(\theta)=a\}$ are measurable. All of this is bundled in a structure `Model`.
--
--   **Histories and algorithms.** A history of length $t$ is $\mathbb H_t=((x_1,y_1),\dots,(x_t,y_t))$. An algorithm is a rule $\pi$ that, after each history $h$ of length $t$, selects the next action with probabilities $\pi_t(a\mid h)\ge 0$ summing to $1$ over $a$ (an adaptive, possibly randomized rule). Given $\theta$, the probability of a history $h$ of length $t$ is
--   $$\ell_t(\theta,h)=\prod_{s=1}^{t}\pi_{s-1}(x_s\mid h_{s-1})\,q_\theta(y_s\mid x_s),$$
--   where $h_{s-1}$ is the prefix of $h$ of length $s-1$. The joint law of $(\theta,\mathbb H_t)$ is $P(d\theta)\,\ell_t(\theta,h)$; in particular $\mathbb P(\mathbb H_t=h)=\int\ell_t(\theta,h)\,P(d\theta)$ and $\mathbb P(x^*=a,\mathbb H_t=h)=\int \mathbf 1\{x^*(\theta)=a\}\,\ell_t(\theta,h)\,P(d\theta)$.
--
--   **Regret.** The expected single-period regret in period $t$ is $\mathbb E[\mu(x^*,\theta)-\mu(x_t,\theta)]$ under the joint law of $(\theta,\mathbb H_t)$, and the expected cumulative (Bayesian) regret over $T$ periods is
--   $$\mathbb E[\mathrm{Regret}(T)]=\mathbb E\Big[\sum_{t=1}^T\big(\mu(x^*,\theta)-\mu(x_t,\theta)\big)\Big],$$
--   under the joint law of $(\theta,\mathbb H_T)$.
--
--   **Information quantities** (natural logarithms throughout). The entropy of the prior distribution of the optimal action is
--   $$H(x^*)=-\sum_{a\in\mathcal X}\mathbb P(x^*=a)\log\mathbb P(x^*=a).$$
--   The conditional mutual information between $x^*$ and the period-$t$ observation $z=(x_t,y_t)$ given $\mathbb H_{t-1}$, averaged over $\mathbb H_{t-1}$, is
--   $$I(x^*;(x_t,y_t)\mid\mathbb H_{t-1})=\sum_{h}\sum_{a}\sum_{z}\mathbb P(x^*=a,\mathbb H_t=hz)\,\log\frac{\mathbb P(x^*=a,\mathbb H_t=hz)\,\mathbb P(\mathbb H_{t-1}=h)}{\mathbb P(x^*=a,\mathbb H_{t-1}=h)\,\mathbb P(\mathbb H_t=hz)},$$
--   where $h$ ranges over histories of length $t-1$ and $hz$ is $h$ extended by $z$; terms with vanishing leading probability are $0$. The information ratio (8.7) is
--   $$\Gamma_t=\frac{\big(\mathbb E[\mu(x^*,\theta)-\mu(x_t,\theta)]\big)^2}{I(x^*;(x_t,y_t)\mid\mathbb H_{t-1})}.$$
--
--   These objects are what the regret bound (8.8) and its proof on p. 76 are about.
--
--   **Formalization Note** The tutorial allows infinite action sets and general outcomes; here $\mathcal X$ and $\mathcal Y$ are finite, which makes $H(x^*)$ and every mutual information a finite sum, while $\Theta$ stays a general measurable space. The outcome kernel $q_\theta(\cdot\mid x)$ of §4 is used in place of the representation $y_t=g(x_t,\theta,w_t)$ of p. 70; both describe the same family of laws. A randomized algorithm is a behavioural policy `Policy X Y`, and `IsPolicy` says its values are probability vectors. Periods are 0-based: tutorial period $t$ is Lean period $s=t-1$, and `periodRegret`, `condMutualInfo` and `infoRatio` take $s$. Measurability of $x^*$ is stated as measurability of its level sets, since $\mathcal X$ carries no σ-algebra. In `condMutualInfo`, whenever the leading probability is positive every probability inside the logarithm is positive, so Lean's conventions $\log 0=0$ and $x/0=0$ never enter; the term is $0$ exactly when the leading probability is $0$. `infoRatio` returns $0$ when the mutual information is $0$ (Lean's $x/0=0$); it is used only under the hypothesis that every mutual information is positive.
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), pp. 18–19 (§4, (4.1)), pp. 70–71 (§8.1.2, Problem Formulation), p. 75 ((8.7) and footnote 1), p. 76 (H(x*) in (8.8))

import Mathlib

/-!
Russo, Van Roy, Kazerouni, Osband, Wen, *A Tutorial on Thompson Sampling*,
Found. Trends Mach. Learn. 11(1) (2018), §4 (pp. 18–19) and §8.1.2 (pp. 70–71, 75–76).

The Bayesian online decision problem with finite action set `X` and finite outcome set `Y`,
a general measurable parameter space `Θ` with prior `P`, outcome kernel `q θ x y = q_θ(y | x)`,
known reward `r`, mean reward `μ(x, θ)`, optimal action `x* = xStar θ`; histories, algorithms
(behavioural policies), the joint law of `(θ, ℍ_t)`, per-period and cumulative Bayesian regret,
the entropy `H(x*)` of the prior law of `x*`, the conditional mutual information
`I(x*; (x_t, y_t) | ℍ_{t-1})` and the information ratio (8.7).

Periods: tutorial period `t = 1, …, T` is Lean period `s = t - 1 : Fin T`; `ℍ_{t-1}` is the
history of length `s`.
-/

open MeasureTheory

noncomputable section

namespace TSTutorial.InfoRatio

variable {X Y Θ : Type}

/-- Mean reward `μ(x, θ) = 𝔼[r(y) | θ, x] = ∑_y q_θ(y | x) r(y)` (p. 71; (4.1), p. 19). -/
def mu [Fintype Y] (q : Θ → X → Y → ℝ) (r : Y → ℝ) (x : X) (θ : Θ) : ℝ :=
  ∑ y, q θ x y * r y

/-- The online decision problem of §4 / §8.1.2: a prior `P` on the parameter `θ`, an outcome
kernel `q θ x · = q_θ(· | x)` (a probability vector on `Y`, measurable in `θ`), a known reward
function `r`, and a selector `xStar θ ∈ argmax_x μ(x, θ)` whose fibres are measurable. -/
structure Model (X Y Θ : Type) [Fintype X] [Fintype Y] [MeasurableSpace Θ] where
  /-- the prior distribution of `θ` -/
  P : Measure Θ
  P_prob : IsProbabilityMeasure P
  /-- the outcome kernel: `q θ x y = q_θ(y | x)` -/
  q : Θ → X → Y → ℝ
  q_nonneg : ∀ θ x y, 0 ≤ q θ x y
  q_sum_one : ∀ θ x, ∑ y, q θ x y = 1
  q_measurable : ∀ x y, Measurable (fun θ => q θ x y)
  /-- the known reward function `r(y)` -/
  r : Y → ℝ
  /-- the optimal action `x* = xStar θ` -/
  xStar : Θ → X
  xStar_measurable : ∀ a, MeasurableSet (xStar ⁻¹' {a})
  xStar_optimal : ∀ θ x, mu q r x θ ≤ mu q r (xStar θ) θ

/-- A history of length `t`: the actions and outcomes `(x_1, y_1), …, (x_t, y_t)` (`ℍ_t`). -/
abbrev Hist (X Y : Type) (t : ℕ) : Type := Fin t → X × Y

/-- An algorithm, as a behavioural policy: `π t h a` is the probability of selecting action `a`
in the period after history `h` of length `t`. -/
abbrev Policy (X Y : Type) : Type := (t : ℕ) → Hist X Y t → X → ℝ

/-- `π` assigns a probability vector on `X` to every history. -/
def IsPolicy [Fintype X] (π : Policy X Y) : Prop :=
  (∀ t h a, 0 ≤ π t h a) ∧ (∀ t h, ∑ a, π t h a = 1)

/-- The prefix of length `s` of a history of length `t ≥ s`. -/
def histPrefix {t : ℕ} (h : Hist X Y t) (s : ℕ) (hs : s ≤ t) : Hist X Y s :=
  fun i => h (Fin.castLE hs i)

variable [Fintype X] [Fintype Y] [MeasurableSpace Θ]

/-- Likelihood of the history `h` of length `t` given `θ` under algorithm `π`:
`∏_s π(x_s | ℍ_{s-1}) q_θ(y_s | x_s)`. -/
def lik (M : Model X Y Θ) (π : Policy X Y) (t : ℕ) (θ : Θ) (h : Hist X Y t) : ℝ :=
  ∏ s : Fin t, π s.val (histPrefix h s.val s.isLt.le) (h s).1 * M.q θ (h s).1 (h s).2

/-- `ℙ(ℍ_t = h)` under the joint law of `θ` and the history. -/
def histProb (M : Model X Y Θ) (π : Policy X Y) (t : ℕ) (h : Hist X Y t) : ℝ :=
  ∫ θ, lik M π t θ h ∂M.P

/-- `ℙ(x* = a, ℍ_t = h)` under the joint law. -/
def jointProb [DecidableEq X] (M : Model X Y Θ) (π : Policy X Y) (t : ℕ) (a : X)
    (h : Hist X Y t) : ℝ :=
  ∫ θ, (if M.xStar θ = a then (1 : ℝ) else 0) * lik M π t θ h ∂M.P

/-- Expected single-period regret `𝔼[μ(x*, θ) − μ(x_t, θ)]` in Lean period `s`
(tutorial period `t = s + 1`): an expectation under the joint law of `(θ, ℍ_{s+1})`, where
`x_t` is the last action of the history. -/
def periodRegret (M : Model X Y Θ) (π : Policy X Y) (s : ℕ) : ℝ :=
  ∫ θ, ∑ h : Hist X Y (s + 1),
    lik M π (s + 1) θ h * (mu M.q M.r (M.xStar θ) θ - mu M.q M.r (h (Fin.last s)).1 θ) ∂M.P

/-- Expected cumulative (Bayesian) regret `𝔼[Regret(T)] = 𝔼[∑_{t=1}^T (μ(x*, θ) − μ(x_t, θ))]`
(p. 71), an expectation under the joint law of `(θ, ℍ_T)`. -/
def expRegret (M : Model X Y Θ) (π : Policy X Y) (T : ℕ) : ℝ :=
  ∫ θ, ∑ h : Hist X Y T,
    lik M π T θ h * ∑ s : Fin T, (mu M.q M.r (M.xStar θ) θ - mu M.q M.r (h s).1 θ) ∂M.P

/-- The prior probability `ℙ(x* = a)`. -/
def starProb (M : Model X Y Θ) (a : X) : ℝ :=
  (M.P (M.xStar ⁻¹' {a})).toReal

/-- The entropy `H(x*) = −∑_a ℙ(x* = a) log ℙ(x* = a)` of the prior distribution of the optimal
action, in nats. -/
def entropyStar (M : Model X Y Θ) : ℝ :=
  ∑ a, Real.negMulLog (starProb M a)

/-- The conditional mutual information `I(x*; (x_t, y_t) | ℍ_{t-1})` for Lean period `s`
(tutorial period `t = s + 1`), averaged over `ℍ_{t-1}` as in (8.7), in nats:
`∑_{h,a,z} ℙ(a, h⌢z) log (ℙ(a, h⌢z) ℙ(h) / (ℙ(a, h) ℙ(h⌢z)))`.
Terms with `ℙ(a, h⌢z) = 0` vanish (the convention `0 log 0 = 0`). -/
def condMutualInfo [DecidableEq X] (M : Model X Y Θ) (π : Policy X Y) (s : ℕ) : ℝ :=
  ∑ h : Hist X Y s, ∑ a : X, ∑ z : X × Y,
    jointProb M π (s + 1) a (Fin.snoc (α := fun _ => X × Y) h z) *
      Real.log (jointProb M π (s + 1) a (Fin.snoc (α := fun _ => X × Y) h z) * histProb M π s h /
        (jointProb M π s a h * histProb M π (s + 1) (Fin.snoc (α := fun _ => X × Y) h z)))

/-- The information ratio (8.7): `Γ_t = (𝔼[μ(x*, θ) − μ(x_t, θ)])² / I(x*; (x_t, y_t) | ℍ_{t-1})`
for Lean period `s` (tutorial period `t = s + 1`). Lean's `x / 0 = 0` makes it `0` when the mutual
information vanishes; it is only used where the mutual information is positive. -/
def infoRatio [DecidableEq X] (M : Model X Y Θ) (π : Policy X Y) (s : ℕ) : ℝ :=
  periodRegret M π s ^ 2 / condMutualInfo M π s

end TSTutorial.InfoRatio


