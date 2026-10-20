-- Prove2me | Definitions.Def_DynkinAsymInfo_Linear_AbstractGame
-- name    : DynkinAsymInfo_Linear_AbstractGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:15:54.821342+00:00
-- url     : https://prove2.me/theorems/82802ba9-6906-40f2-81d1-5bc70870ef04
-- title:
--   §2 — abstract two-filtration randomised stopping game
-- statement:
--   An abstract **randomised Dynkin game** has a probability measure $P$, an observation filtration for a maximising player, a possibly larger filtration for a minimising player, a state process $Y_t$, and a uniform randomisation device $U$. The maximiser chooses an almost surely finite stopping time $\tau$ for the first filtration. The minimiser chooses a right continuous, nondecreasing, adapted control $\Gamma$ with values in $[0,1]$ and $\Gamma_{0-}=0$. The control generates $\gamma=\inf\{t\ge0:\Gamma_t>U\}$.
--
--   For nonnegative payoffs $f,g$, the realised payoff is $f(Y_\tau)$ when $\tau<\gamma$ and $g(Y_\gamma)$ when $\gamma\le\tau<\infty$ or $\gamma<\tau$; simultaneous infinity pays zero. Its nonnegative extended expectation is $J(\tau,\Gamma)$. A saddle point satisfies
--   $$J(\tau,\Gamma^*)\le J(\tau^*,\Gamma^*)\le J(\tau^*,\Gamma)$$
--   for every admissible pair.
--
--   This model-independent frame is reused by the paper-specific GBM game.
--
--   **Formalization Note.** A finite tie pays $g$. The frame is raw data; the paper-specific probability and independence assumptions are supplied when it is instantiated. The actual theorem statements restrict $0\le f\le g$, avoiding clipping by `ENNReal.ofReal`.
-- source:
--   De Angelis, Ekström, Glover, Dynkin Games with Incomplete and Asymmetric Information, arXiv:1810.07674v5, pp. 4–5, §2 and Definition 2.4

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace DynkinAsymInfo.Linear
set_option autoImplicit false

/-- An abstract two-filtration randomised Dynkin game. The maximiser observes `Fmax`,
the minimiser observes `Fmin`, and the minimiser's monotone control is converted to
a stopping time by the uniform device `U`. No model dynamics are built into this
frame. De Angelis, Ekström, Glover, arXiv:1810.07674v5, pp. 4–5, §2. -/
structure RandomisedDynkinFrame (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  Fmax : Filtration ℝ≥0 ‹MeasurableSpace Ω›
  Fmin : Filtration ℝ≥0 ‹MeasurableSpace Ω›
  U : Ω → ℝ
  Y : ℝ≥0 → Ω → ℝ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An a.s. finite stopping time for the maximiser's filtration, p. 4. -/
def RandomisedDynkinFrame.InT (fr : RandomisedDynkinFrame Ω)
    (tau : Ω → WithTop ℝ≥0) : Prop :=
  IsStoppingTime fr.Fmax tau ∧ ∀ᵐ a ∂fr.P, tau a ≠ ⊤

/-- A monotone right-continuous [0,1]-valued control adapted to a filtration.
The process may have an atom at zero, corresponding to `Γ_{0-}=0`, p. 4. -/
def RandomisedDynkinFrame.InA (fr : RandomisedDynkinFrame Ω)
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (G : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ t, Measurable[F t] (G t)) ∧
  ∀ᵐ a ∂fr.P, Monotone (fun t => G t a) ∧
    (∀ t, ContinuousWithinAt (fun s => G s a) (Set.Ici t) t) ∧
    0 ≤ G 0 a ∧ ∀ t, G t a ≤ 1

/-- The strict crossing-time convention of (2), p. 5. -/
noncomputable def randomisedTime (U : Ω → ℝ) (G : ℝ≥0 → Ω → ℝ)
    (a : Ω) : WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0) (_ : U a < G t a), (t : WithTop ℝ≥0)

noncomputable def RandomisedDynkinFrame.randST (fr : RandomisedDynkinFrame Ω)
    (G : ℝ≥0 → Ω → ℝ) (a : Ω) : WithTop ℝ≥0 :=
  randomisedTime fr.U G a

/-- The realised payoff: the maximiser receives `f` if first and `g` on a
finite tie or if the minimiser stops first; joint infinity pays zero. -/
noncomputable def RandomisedDynkinFrame.pay (fr : RandomisedDynkinFrame Ω)
    (f g : ℝ → ℝ) (tau gamma : Ω → WithTop ℝ≥0) (a : Ω) : ℝ≥0∞ :=
  if tau a < gamma a then ENNReal.ofReal (f (fr.Y (tau a).untopA a))
  else if gamma a ≠ ⊤ then ENNReal.ofReal (g (fr.Y (gamma a).untopA a))
  else 0

/-- Expected payoff of the abstract game, (5), p. 5. -/
noncomputable def RandomisedDynkinFrame.J (fr : RandomisedDynkinFrame Ω)
    (f g : ℝ → ℝ) (tau : Ω → WithTop ℝ≥0) (G : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ a, fr.pay f g tau (fr.randST G) a ∂fr.P

/-- Saddle point over the entire two-player strategy classes,
Definition 2.4, p. 5. -/
def RandomisedDynkinFrame.IsSaddle (fr : RandomisedDynkinFrame Ω)
    (f g : ℝ → ℝ) (taus : Ω → WithTop ℝ≥0) (Gs : ℝ≥0 → Ω → ℝ) : Prop :=
  fr.InT taus ∧ fr.InA fr.Fmin Gs ∧
  ∀ tau G, fr.InT tau → fr.InA fr.Fmin G →
    fr.J f g tau Gs ≤ fr.J f g taus Gs ∧
    fr.J f g taus Gs ≤ fr.J f g taus G

end DynkinAsymInfo.Linear


