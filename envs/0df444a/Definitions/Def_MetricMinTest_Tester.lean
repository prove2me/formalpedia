-- Prove2me | Definitions.Def_MetricMinTest_Tester
-- name    : MetricMinTest_Tester
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:39.934862+00:00
-- url     : https://prove2.me/theorems/4aba489c-cd63-4771-bceb-ddc65dfc05ca
-- title:
--   Sequential tester with private randomness
-- statement:
--   A **sequential tester** first draws private randomness $\xi$ from a probability space $(\Xi,\mu_\xi)$, independent of all observations. At each step it either stops or chooses the next index to query, as a function of $\xi$ and the history of (index, observation) pairs so far. When it stops at time $\tau$ it returns a decision $A\in\{\text{accept},\text{reject}\}$, again a function of $\xi$ and the history. Queries, stopping and decision may all be randomized through $\xi$.
--
--   **Formalization Note** The query rule returns `none` to stop. That $\mu_\xi$ is a probability measure is part of validity.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §2, p.6

import Mathlib

namespace MetricMinTest

/-- **Sequential tester.** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027
submission (manuscript sha256 dcece193…ad32bb), §2 p.6: "At query t, the tester chooses Iₜ from
the past … It stops at τ and returns A ∈ {accept, reject}", with private randomization
("A deterministic budget permits private randomization").

**Formalization Note.** Private randomness is a measurable space `Ξ` with a measure `μξ` (a
probability measure in every valid tester, see `Tester.IsValid`), drawn once and independently of
the observations. Given `ξ` and the history so far (the list of `(index, observation)` pairs),
`next` returns the next index to query, or `none` to stop; `accept` is the decision made at the
stopping time. Queries, stopping and decision may all depend on `ξ`. -/
structure Tester (ι : Type) where
  /-- The space of private randomness. -/
  Ξ : Type
  [mΞ : MeasurableSpace Ξ]
  /-- The law of the private randomness. -/
  μξ : MeasureTheory.Measure Ξ
  /-- The query rule: next index, or `none` to stop. -/
  next : Ξ → List (ι × ℝ) → Option ι
  /-- The decision (`true` = accept) as a function of `ξ` and the final history. -/
  accept : Ξ → List (ι × ℝ) → Bool

attribute [instance] Tester.mΞ

end MetricMinTest


