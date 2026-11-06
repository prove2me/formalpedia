-- Prove2me | Definitions.Def_MetricMinTest_RoundTester
-- name    : MetricMinTest_RoundTester
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:40.996361+00:00
-- url     : https://prove2.me/theorems/98ab2dc7-43b1-496c-86dd-fc88197ccab1
-- title:
--   Round-adaptive tester with $q$ rounds
-- statement:
--   A tester with $q$ **rounds** first draws private randomness $\xi$, independent of all observations. Then, for $s=1,\dots,q$, it chooses a count vector $n^{(s)}\in\mathbb Z_{\ge0}^k$ as a function of $\xi$ and of the observations from rounds $1,\dots,s-1$, and receives $n^{(s)}_j$ fresh observations from each index $j$. Its decision may depend on $\xi$ and on all observations. There is no stopping inside a round. A one-round tester is a **nonadaptive** tester (Definition 4.4): it queries each $j$ exactly $n_j(\xi)$ times.
--
--   **Formalization Note** Rounds are numbered from $0$. Counts and decision are written as functions of the whole observation table; that they read only observed entries is the adaptedness condition, which is part of validity.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition C.6, p.25; Definition 4.4, p.9

import Mathlib

namespace MetricMinTest

/-- **Round-adaptive tester with `q` rounds** (Definition C.6). Chen–Fang, *Minimum-Mean Testing
under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb),
Definition C.6, p.25: "A tester has q rounds if it first draws private randomness ξ, independent
of all observations, and then, for s = 1, …, q, chooses a count vector n^(s) ∈ ℤ^k_{≥0} as a
function of ξ and of the observations from rounds 1, …, s − 1, and receives n^(s)_j fresh
observations from each index j. Its decision may depend on ξ and on all observations." A
one-round tester is a nonadaptive tester (Definition 4.4, p.9).

**Formalization Note.** In the stack-of-streams model (`streamLaw`), round `s` (0-based, `Fin q`)
reads the next `counts s ξ ω j` unread entries of stream `j`. `counts` and `accept` are written as
functions of the whole table `ω`; that they read only observed entries is the adaptedness
condition `RoundTester.IsAdapted`, part of validity. -/
structure RoundTester (ι : Type) (q : ℕ) where
  /-- The space of private randomness. -/
  Ξ : Type
  [mΞ : MeasurableSpace Ξ]
  /-- The law of the private randomness. -/
  μξ : MeasureTheory.Measure Ξ
  /-- The count vector `n^(s)` of round `s`. -/
  counts : Fin q → Ξ → (ι → ℕ → ℝ) → ι → ℕ
  /-- The decision (`true` = accept). -/
  accept : Ξ → (ι → ℕ → ℝ) → Bool

attribute [instance] RoundTester.mΞ

end MetricMinTest


