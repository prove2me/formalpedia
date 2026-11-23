-- Prove2me | Definitions.Def_JSQHalfinWhitt_Tightness_Supplement_Diffusion
-- name    : JSQHalfinWhitt_Tightness_Supplement_Diffusion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:14:46.030909+00:00
-- url     : https://prove2.me/theorems/8f0ebad1-4546-4d2d-8c83-abfd1e968114
-- title:
--   The reflected JSQ diffusion (2.1) as a Markov family
-- statement:
--   Let $\Omega=(-\infty,0]\times[0,\infty)$, let $\beta\in\mathbb R$, and let $F$ be a continuous-time strong Markov family on $\Omega$, with transition probabilities $P_t(y,\cdot)$, probability measure $P$, adapted paths $Y^y$, and the usual filtrations $\mathcal F_t^y$. The domain is the published $\Omega$; the general Markov-family structure is also published separately.
--
--   The predicate $\operatorname{IsJSQDiffusion}(\beta,F)$ means that, for every initial state $y\in\Omega$, there are a standard real $\mathcal F^y$-Brownian motion $W^y$ and an adapted regulator $U^y$ such that, almost surely simultaneously at all $t\ge0$,
--   $$
--   Y_1^y(t)=y_1+\sqrt2 W^y(t)-\beta t+\int_0^t(-Y_1^y(s)+Y_2^y(s))\,ds-U^y(t),\qquad
--   Y_2^y(t)=y_2+U^y(t)-\int_0^tY_2^y(s)\,ds.
--   $$
--   The paths $Y^y$ and $U^y$ are continuous, $U^y(0)=0$, and $U^y$ is nondecreasing, hence nonnegative. It increases only where $Y_1^y=0$. This last condition is encoded by constancy of $U^y$ on every closed interval on which $Y_1^y<0$; for continuous monotone regulators it is equivalent to $\int_0^\infty 1(Y_1^y(t)<0)\,dU^y(t)=0$. The state subtype requires $Y^y(t)\in\Omega$ at every time.
--
--   This is a specification of the stochastic equation, including its actual transition probabilities, separate from any recurrence claim. Existence, uniqueness in law and positive Harris recurrence are conclusions of the companion theorem, rather than fields of this definition. The Brownian and general Markov objects are imported, not redefined. No stationary distribution or Lyapunov certificate is assumed.
--
--   **Formalization Note** Time is $\mathbb R_{\ge0}$. Integrals are ordinary real interval integrals after the continuous extension $s\mapsto Y^y(s^+)$, where $s^+=\max(s,0)$. On $[0,t]$ this changes nothing, and continuity guarantees interval integrability. The predicate itself permits any real $\beta$; the theorem assumes exactly $\beta>0$.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), pp. 4–5, (1.4), (2.1); repeated pp. 15–16

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_PDE
import Definitions.Def_BramsonQueueing_FIFOKelly_Markov
import Definitions.Def_EllsbergLearning_IsBrownianWrt

namespace JSQHalfinWhitt.Tightness.Supplement

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The full closed domain Ω of (1.4), using the published definition. -/
abbrev State := ↥JSQHalfinWhitt.Tightness.Omega

/-- Pathwise integral equations (2.1), with regulator supported on {Y₁ = 0}.
For a continuous nondecreasing regulator, constancy on every closed interval
where Y₁ < 0 is equivalent to ∫ 1(Y₁ < 0) dU = 0. The interval integrands
are continuous, hence interval integrable; no default Bochner integral is used.
The domain subtype enforces both Y₁ ≤ 0 and Y₂ ≥ 0 at every time. -/
def IsReflectedPath (β : ℝ) (y : State) (w : ℝ≥0 → ℝ)
    (z : ℝ≥0 → State) (u : ℝ≥0 → ℝ) : Prop :=
  Continuous z ∧ Continuous u ∧ u 0 = 0 ∧ Monotone u ∧
    (∀ s t : ℝ≥0, s ≤ t →
      (∀ r ∈ Set.Icc s t, ((z r : State) : ℝ × ℝ).1 < 0) → u s = u t) ∧
    ∀ t : ℝ≥0,
      ((z t : State) : ℝ × ℝ).1 = (y : ℝ × ℝ).1 + Real.sqrt 2 * w t - β * t +
        (∫ s in (0 : ℝ)..(t : ℝ),
          (-((z (Real.toNNReal s) : State) : ℝ × ℝ).1 +
            ((z (Real.toNNReal s) : State) : ℝ × ℝ).2)) - u t ∧
      ((z t : State) : ℝ × ℝ).2 = (y : ℝ × ℝ).2 + u t -
        ∫ s in (0 : ℝ)..(t : ℝ), ((z (Real.toNNReal s) : State) : ℝ × ℝ).2

/-- A realization of the reflected JSQ diffusion (2.1) as an actual strong Markov
family. Brownian noise is relative to the family's usual filtration, and U is
adapted. Neither an invariant distribution, recurrence, uniqueness, nor a
Lyapunov inequality is included in this definition. Existence, uniqueness in law,
and positive recurrence are obligations of theorem_3, not hypotheses on β. -/
def IsJSQDiffusion {Ξ : Type} [mΞ : MeasurableSpace Ξ] (β : ℝ)
    (F : BramsonQueueing.FIFOKelly.MarkovFamily State Ξ) : Prop :=
  ∃ (W U : State → ℝ≥0 → Ξ → ℝ),
    (∀ y, EllsbergLearning.IsBrownianWrt
      ({ seq := F.filtration y, mono' := F.filtration_mono y,
         le' := F.filtration_le y } : Filtration ℝ≥0 mΞ) F.probability (W y)) ∧
    (∀ y t, @Measurable Ξ ℝ (F.filtration y t) _ (U y t)) ∧
    ∀ y, ∀ᵐ ω ∂F.probability,
      IsReflectedPath β y (fun t => W y t ω)
        (fun t => F.path y t ω) (fun t => U y t ω)

end JSQHalfinWhitt.Tightness.Supplement


