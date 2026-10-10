-- Prove2me | Definitions.Def_GraphLQGame_DenseApprox_FBrownian
-- name    : GraphLQGame_DenseApprox_FBrownian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:24:39.141892+00:00
-- url     : https://prove2.me/theorems/f004ae2d-e747-44ad-badc-a8b0daba4528
-- title:
--   Real-valued $\mathbb F$-Brownian motion on a filtered probability space
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb F,\mathbb P)$ be a filtered probability space with $\mathbb F=(\mathcal F_t)_{t\ge0}$. A real process $W=(W(t))_{t\ge0}$ is an **$\mathbb F$-Brownian motion** if
--
--   1. $W$ is a standard Brownian motion under $\mathbb P$: $W(0)=0$, its finite-dimensional laws are centred Gaussian with $\mathrm{Cov}(W(s),W(t))=s\wedge t$, and its paths are almost surely continuous;
--   2. $W$ is $\mathbb F$-adapted;
--   3. for every $t$, the increments $(W(r)-W(t))_{r\ge t}$ are independent of $\mathcal F_t$.
--
--   This is the noise of the one-player control problem of Lemma 7.2.
--
--   **Formalization Note** Time is indexed by $\mathbb R_{\ge0}$, and the Brownian property is Mathlib's `IsBrownianReal`. The same pattern is used for the $d$-dimensional $\mathbb F$-Brownian motion of other mean-field-game drafts on the platform; it is restated here in dimension one.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), Lemma 7.2, p. 40 ("any filtered probability space supporting an F′-Brownian motion W")

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GraphLQGame.DenseApprox

/-- A real-valued `𝔽`-Brownian motion on a filtered probability space `(Ω, 𝓕, 𝔽, P)`, as in the
hypotheses of Lemma 7.2 (Lacker–Soret, arXiv:2005.14102v2, p. 40): `W` is a standard real Brownian
motion under `P` (Mathlib's `IsBrownianReal`: Gaussian finite-dimensional laws with covariance
`s ∧ t`, `W 0 = 0` a.s., almost surely continuous paths), it is `𝔽`-adapted, and for every `t`
its increments `(W r − W t)_{r ≥ t}` are independent of `𝓕_t`.

Formalization Note: time is `ℝ≥0`; the same pattern as the `𝔽`-Brownian motion of the
`ClosedLoopMFG.MarkovNash` drafts, restated here in dimension one. -/
def IsFBrownianReal {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) : Prop :=
  IsBrownianReal W P ∧
  (∀ t, Measurable[𝓕 t] (W t)) ∧
  ∀ t, Indep (𝓕 t)
    (MeasurableSpace.comap (fun ω (r : Set.Ici t) => W r ω - W t ω) inferInstance) P

end GraphLQGame.DenseApprox


