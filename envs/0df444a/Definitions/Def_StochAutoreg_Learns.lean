-- Prove2me | Definitions.Def_StochAutoreg_Learns
-- name    : StochAutoreg_Learns
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:16:22.747384+00:00
-- url     : https://prove2.me/theorems/eedc33d3-faef-4821-af86-0eb1188cee99
-- title:
--   $n$ samples suffice to $(\varepsilon,\delta)$-learn a class
-- statement:
--   Under a supervision model, with sample law depending on the target $g$ and the prompt law $P$, **$n$ samples suffice to $(\varepsilon,\delta)$-learn** the targets of $\mathcal F$ when there is one learner $A$ such that, for every $g\in\mathcal F$ and every $P$,
--
--   $$\Pr\Bigl[\mathbb E_{X\sim P}\mathrm{KL}\bigl(q_g(X)\|A(\text{sample},\text{seed})(X)\bigr)\le\varepsilon\Bigr]\ge1-\delta.$$
--
--   The learner comes before $g$ and $P$: it knows the class, the supervision model and $\varepsilon,\delta,n$, and neither the target nor the prompt law.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §1.1, p.3

import Mathlib
import Definitions.Def_StochAutoreg_Generator
import Definitions.Def_StochAutoreg_risk
import Definitions.Def_StochAutoreg_Learner
import Definitions.Def_StochAutoreg_iidSeedMeasure

namespace StochAutoreg

/-- `n` samples **suffice to `(ε, δ)`-learn** the targets of a class `F`: one learner, fixed before the
target and the prompt law, outputs with probability at least `1 - δ` a predictor of error at most `ε`, for
every `g ∈ F` and every prompt law `P`. Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §1.1, p.3 ("A learner (ε, δ)-learns a class" and "uniformly
over any distribution P on Σ⋆ and g⋆ ∈ F").

**Formalization Note.** The order is `∃` learner, then `∀ g ∈ F`, `∀ P`. The learner may depend on `F`, on
the supervision model and on `ε, δ, n`, and on nothing else. -/
def Learns {S : Type} [MeasurableSpace S] (F : Set Generator)
    (law : Generator → PMF (List Bool) → PMF S) (target : Generator → List Bool → ℝ)
    (ε δ : ℝ) (n : ℕ) : Prop :=
  ∃ A : Learner S n, ∀ g ∈ F, ∀ P : PMF (List Bool),
    ENNReal.ofReal (1 - δ) ≤ iidSeedMeasure (law g P) n
      {w | risk P (target g) (A.run w.1 w.2) ≤ ENNReal.ofReal ε}

end StochAutoreg


