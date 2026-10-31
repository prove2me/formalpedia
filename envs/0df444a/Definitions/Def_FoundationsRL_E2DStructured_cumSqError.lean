-- Prove2me | Definitions.Def_FoundationsRL_E2DStructured_cumSqError
-- name    : FoundationsRL_E2DStructured_cumSqError
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:44.572588+00:00
-- url     : https://prove2.me/theorems/651ac9bf-0162-4856-9541-1062595e8640
-- title:
--   The cumulative squared estimation error
-- statement:
--   For distributions $p^t$ and estimates $\hat f^t$, the cumulative squared error against a function $f$ up to round $T$ is
--   $$\sum_{t=1}^T\mathbb E_{\pi^t\sim p^t}\big[(\hat f^t(\pi^t)-f(\pi^t))^2\big].$$
--   It appears with $f=f^\star$ in the guarantee of an online regression oracle and with a generic $f$ in the confidence sets of §4.4.1.
--
--   **Formalization Note** Rounds are indexed from $0$, so the sum over $i<t$ is the error up to $t$, empty at the first round.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Definition 7, p. 64; §4.4.1, p. 75

import Mathlib
import Definitions.Def_FoundationsRL_E2DStructured_sqError

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- The cumulative squared estimation error
`∑_{t<T} E_{π^t∼p^t}[(f̂^t(π^t) − f(π^t))²]` of a sequence of estimates against `f`
(Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.2, Definition 7, p. 64; §4.4.1, p. 75).

**Formalization Note.** Rounds are indexed from `0`, so the sum over `i < t` in the definition of
`F^t` is `cumSqError t`, which is empty at the first round. -/
noncomputable def cumSqError {D : Type*} [MeasurableSpace D] (T : ℕ)
    (p : ℕ → ProbabilityMeasure D) (fhat : ℕ → D → ℝ) (f : D → ℝ) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range T, sqError (p t) (fhat t) f

end FoundationsRL.E2DStructured


