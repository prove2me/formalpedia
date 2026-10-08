-- Prove2me | Definitions.Def_TSTutorial_UCBDecomp_Setting
-- name    : TSTutorial_UCBDecomp_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:46.458003+00:00
-- url     : https://prove2.me/theorems/82084178-a7b0-4dce-bc7b-a63ad21550a5
-- title:
--   §4 and §8.1.2, pp. 18–19, 70–73 — the Bayesian model, Thompson sampling and regret terms
-- statement:
--   Consider a Bayesian online decision problem with a finite nonempty action set $\mathcal X$, a finite outcome set $Y$, and a measurable parameter space $\Theta$. A probability measure $P$ describes prior uncertainty about $\theta\in\Theta$. If action $x$ is selected, the outcome $y$ has probability $q_\theta(y\mid x)$ and earns the known reward $r(y)$. Thus the mean reward is
--
--   $$
--   \mu(x,\theta)=\sum_{y\in Y}q_\theta(y\mid x)r(y).
--   $$
--
--   A measurable selector $x^*(\theta)$ maximizes $\mu(\cdot,\theta)$, using one fixed tie-break. A history $H_t$ records the first $t$ action–outcome pairs, and a behavioural policy $\pi$ gives an action distribution after each history. The joint law draws $\theta\sim P$ and then generates each action using $\pi$ and each outcome using $q_\theta$. This law defines the probability of each history, expected regret in period $t$, and expected cumulative regret over $T$ periods.
--
--   The posterior probability of $x^*=a$ after a history $h$ is computed from the prior and the product of the outcome likelihoods. Thompson sampling draws a parameter from that posterior and plays its selected optimal action; its action probability is this posterior probability whenever the observed history has positive evidence. On impossible histories, the policy may use any action distribution.
--
--   For any real score $U_t(x)$ computed from the past history, the setting also defines the expected pessimism and width terms in the decomposition on p. 73.
--
--   **Formalization Note** Lean uses finite action and outcome types, a general measurable parameter type, and a kernel instead of the paper's equivalent independent-noise representation. The outcome kernel is measurable in $\theta$, and the selected optimum has measurable fibers. Round $s$ in Lean is round $t=s+1$ in the paper. The selector used by Thompson sampling and by regret is the same, including its tie-break.
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), §4 pp. 18–19, (4.1), (4.2), Algorithm 4; §8.1.2 pp. 70–73, (8.4) and display after (8.4)

import Mathlib

open MeasureTheory
open scoped BigOperators

namespace TSTutorial.UCBDecomp

/-- The finite-outcome Bayesian experiment of §4 and §8.1.2. -/
structure Model (X Y Θ : Type*) [Fintype X] [Fintype Y] [MeasurableSpace Θ] where
  prior : Measure Θ
  prior_prob : IsProbabilityMeasure prior
  q : Θ → X → Y → ℝ
  q_nonneg : ∀ θ x y, 0 ≤ q θ x y
  q_sum : ∀ θ x, ∑ y, q θ x y = 1
  q_measurable : ∀ x y, Measurable (fun θ => q θ x y)
  reward : Y → ℝ

variable {X Y Θ : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
  [Fintype Y] [DecidableEq Y] [MeasurableSpace Θ]

/-- Mean reward under parameter `θ`. -/
def mu (m : Model X Y Θ) (x : X) (θ : Θ) : ℝ :=
  ∑ y, m.q θ x y * m.reward y

/-- A measurable, optimal action selected using one fixed tie-break. -/
def IsOptimalSelector (m : Model X Y Θ) (xStar : Θ → X) : Prop :=
  (∀ a, MeasurableSet {θ | xStar θ = a}) ∧
    ∀ θ x, mu m x θ ≤ mu m (xStar θ) θ

/-- The action/outcome history of `t` completed periods. -/
abbrev Hist (X Y : Type*) (t : ℕ) := Fin t → X × Y

/-- The first `s` entries of a length-`t` history. -/
def histPrefix {t : ℕ} (h : Hist X Y t) (s : Fin t) : Hist X Y s :=
  fun i => h (Fin.castLE (Nat.le_of_lt s.isLt) i)

/-- A history with its last entry removed. -/
def init {t : ℕ} (h : Hist X Y (t + 1)) : Hist X Y t :=
  fun i => h i.castSucc

/-- A history extended by one action/outcome pair. -/
def snoc {t : ℕ} (h : Hist X Y t) (z : X × Y) : Hist X Y (t + 1) :=
  Fin.snoc h z

/-- A behavioural action-selection policy. -/
abbrev Policy (X Y : Type*) := (t : ℕ) → Hist X Y t → X → ℝ

def IsPolicy (π : Policy X Y) : Prop :=
  (∀ t h a, 0 ≤ π t h a) ∧ (∀ t h, ∑ a, π t h a = 1)

/-- Outcome likelihood of a fixed history, omitting action-choice factors. -/
def qlik (m : Model X Y Θ) (t : ℕ) (θ : Θ) (h : Hist X Y t) : ℝ :=
  ∏ s : Fin t, m.q θ (h s).1 (h s).2

/-- Joint-history likelihood given `θ`, including the policy's action probabilities. -/
def lik (m : Model X Y Θ) (π : Policy X Y) (t : ℕ) (θ : Θ)
    (h : Hist X Y t) : ℝ :=
  ∏ s : Fin t, π s (histPrefix h s) (h s).1 * m.q θ (h s).1 (h s).2

/-- Probability of a history under the prior, kernel, and policy. -/
noncomputable def histProb (m : Model X Y Θ) (π : Policy X Y)
    (t : ℕ) (h : Hist X Y t) : ℝ :=
  ∫ θ, lik m π t θ h ∂m.prior

/-- Joint probability of the selected optimal action and a history. -/
noncomputable def jointProb (m : Model X Y Θ) (xStar : Θ → X)
    (π : Policy X Y) (t : ℕ) (a : X) (h : Hist X Y t) : ℝ :=
  ∫ θ, (if xStar θ = a then 1 else 0) * lik m π t θ h ∂m.prior

/-- Posterior mass of parameters whose selected optimal action is `a`. -/
noncomputable def postStar (m : Model X Y Θ) (xStar : Θ → X)
    (t : ℕ) (h : Hist X Y t) (a : X) : ℝ :=
  (∫ θ, (if xStar θ = a then 1 else 0) * qlik m t θ h ∂m.prior) /
    ∫ θ, qlik m t θ h ∂m.prior

/-- Algorithm 4: sample a parameter from the posterior and play its selected optimum. -/
def IsThompsonSampling (m : Model X Y Θ) (xStar : Θ → X)
    (π : Policy X Y) : Prop :=
  IsPolicy π ∧ ∀ t (h : Hist X Y t),
    0 < (∫ θ, qlik m t θ h ∂m.prior) →
      ∀ a, π t h a = postStar m xStar t h a

/-- Expected regret in period `s + 1` under the actual length-`s + 1` law. -/
noncomputable def periodRegret (m : Model X Y Θ) (xStar : Θ → X)
    (π : Policy X Y) (s : ℕ) : ℝ :=
  ∫ θ, ∑ h : Hist X Y (s + 1), lik m π (s + 1) θ h *
    (mu m (xStar θ) θ - mu m (h (Fin.last s)).1 θ) ∂m.prior

/-- Bayesian cumulative regret over `T` periods, as defined on p. 71. -/
noncomputable def expRegret (m : Model X Y Θ) (xStar : Θ → X)
    (π : Policy X Y) (T : ℕ) : ℝ :=
  ∫ θ, ∑ h : Hist X Y T, lik m π T θ h *
    ∑ s : Fin T, (mu m (xStar θ) θ - mu m (h s).1 θ) ∂m.prior

/-- The unshifted first term in the p. 73 decomposition. -/
noncomputable def unshiftedPessimism (m : Model X Y Θ) (xStar : Θ → X)
    (π : Policy X Y) (s : ℕ) (U : Hist X Y s → X → ℝ) : ℝ :=
  ∫ θ, ∑ h : Hist X Y (s + 1), lik m π (s + 1) θ h *
    (mu m (xStar θ) θ - U (init h) (h (Fin.last s)).1) ∂m.prior

/-- Pessimism term in the p. 73 Thompson-sampling decomposition. -/
noncomputable def pessimism (m : Model X Y Θ) (xStar : Θ → X)
    (π : Policy X Y) (s : ℕ) (U : Hist X Y s → X → ℝ) : ℝ :=
  ∫ θ, ∑ h : Hist X Y (s + 1), lik m π (s + 1) θ h *
    (mu m (xStar θ) θ - U (init h) (xStar θ)) ∂m.prior

/-- Width term in the p. 73 Thompson-sampling decomposition. -/
noncomputable def width (m : Model X Y Θ) (π : Policy X Y)
    (s : ℕ) (U : Hist X Y s → X → ℝ) : ℝ :=
  ∫ θ, ∑ h : Hist X Y (s + 1), lik m π (s + 1) θ h *
    (U (init h) (h (Fin.last s)).1 - mu m (h (Fin.last s)).1 θ) ∂m.prior

end TSTutorial.UCBDecomp


