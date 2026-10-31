-- Prove2me | Definitions.Def_FoundationsRL_E2DStructured_decObjective
-- name    : FoundationsRL_E2DStructured_decObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:22:20.298599+00:00
-- url     : https://prove2.me/theorems/026cd398-6923-49df-b065-ffc4aa61b704
-- title:
--   The objective of the DEC game
-- statement:
--   For $\gamma\in\mathbb R$, a reward function $f$, a reference model $\hat f$ and $p\in\Delta(\Pi)$, the objective of the DEC game is
--   $$\mathbb E_{\pi\sim p}\big[f(\pi_f)-f(\pi)-\gamma\,(f(\pi)-\hat f(\pi))^2\big],$$
--   regret of the decision minus $\gamma$ times the information gain.
--
--   **Formalization Note** Regret and squared error are computed separately in $[0,\infty]$ and subtracted in the extended reals. With a finite squared error the value is the expectation above. With infinite squared error and finite regret it is $-\infty$, which is also the expectation. If both are infinite the expectation is undefined, and the convention $\infty-\infty=-\infty$ of `EReal` applies; this can occur only when $f$ is unbounded below.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.2, (4.15), p. 65

import Mathlib
import Definitions.Def_FoundationsRL_E2DStructured_expectedGap
import Definitions.Def_FoundationsRL_E2DStructured_sqError

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- The objective of the DEC game,
`E_{π∼p}[f(π_f) − f(π) − γ·(f(π) − f̂(π))²]` (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.2, p. 65, (4.15)).

**Formalization Note.** Regret and information gain are computed separately in `[0, ∞]` and subtracted
in `EReal`. If the squared error is finite the value is the book's. If it is infinite and the regret
is finite the value is `−∞`, the book's expectation. If both are infinite the book's expectation is
`∞ − ∞` and undefined; Lean's `⊤ - ⊤ = ⊥` scores such a `p` as `−∞`. That case needs `f` unbounded
below. -/
noncomputable def decObjective {D : Type*} [MeasurableSpace D] (γ : ℝ) (f fhat : D → ℝ)
    (p : ProbabilityMeasure D) : EReal :=
  (expectedGap f p : EReal) - (γ : EReal) * (sqError p f fhat : EReal)

end FoundationsRL.E2DStructured


