-- Prove2me | Definitions.Def_SDEConvexOpt_IsFBrownian
-- name    : SDEConvexOpt_IsFBrownian
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:25:05.899494+00:00
-- url     : https://prove2.me/theorems/873d4a86-7049-4c23-8a1b-cd9b1c3e8325
-- title:
--   $W$ is an $m$-dimensional Brownian motion with respect to the filtration $(\mathcal F_t)$
-- statement:
--   Let $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},\mathbb P)$ be a filtered probability space. A process $W:\mathbb R_+\times\Omega\to\mathbb R^m$ is an $m$-dimensional $(\mathcal F_t)$-Brownian motion when
--
--   1. $W$ is a standard $m$-dimensional Brownian motion: its coordinates are independent standard real Brownian motions, with continuous paths;
--   2. $W$ is $(\mathcal F_t)$-adapted;
--   3. for $s\le t$, the increment $W(t)-W(s)$ is independent of $\mathcal F_s$.
--
--   This is the driving noise of (SDE) and (A.1).
--
--   **Formalization Note** The standard Brownian motion is the published `EthierKurtz.IsStandardBrownian`; the filtration is a Mathlib `Filtration ℝ≥0`. Item 3 is the standard meaning of a Brownian motion with respect to a filtration; (A.1) states only adaptedness, which alone would not make the Itô integrals martingales.
-- source:
--   Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex optimization, arXiv:2207.02750v1, (SDE), p.2; (A.1), p.34

import Definitions.Def_EthierKurtz_IsStandardBrownian

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SDEConvexOpt

open EthierKurtz

/-- `W` is an `m`-dimensional Brownian motion with respect to the filtration `{𝓕ₜ}`
(Maulen S., Fadili, Attouch, arXiv:2207.02750v1, (SDE), p.2: "W is the m-dimensional Brownian
motion" on the filtered probability space `(Ω, 𝓕, {𝓕ₜ}, ℙ)`; (A.1), p.34: "W is a 𝓕ₜ-adapted
m-dimensional Brownian Motion").

It is a standard `m`-dimensional Brownian motion (published `EthierKurtz.IsStandardBrownian`:
measurable time slices, continuous paths, independent standard real Brownian coordinates),
adapted to `𝓕`, whose increments `W(t) − W(s)`, `s ≤ t`, are independent of `𝓕ₛ`.

**Formalization Note** Time is `ℝ≥0` and the filtration a Mathlib `Filtration ℝ≥0`. The
independence of increments from the past is the standard meaning of a Brownian motion with
respect to a filtration; adaptedness alone would not make the Itô integrals of p.10 martingales. -/
def IsFBrownian {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (W : ℝ≥0 → Ω → SDEState m) : Prop :=
  IsStandardBrownian P W ∧ Adapted ℱ W ∧
    ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance) (ℱ s) P

end SDEConvexOpt


