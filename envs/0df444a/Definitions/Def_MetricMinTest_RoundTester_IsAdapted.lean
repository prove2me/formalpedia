-- Prove2me | Definitions.Def_MetricMinTest_RoundTester_IsAdapted
-- name    : MetricMinTest_RoundTester_IsAdapted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:07.917402+00:00
-- url     : https://prove2.me/theorems/0ded593d-b23c-4fb4-99d0-e25e113fb711
-- title:
--   Adaptedness of a round tester
-- statement:
--   A round tester is **adapted** if
--   1. the counts of round $s$ take the same value on any two observation tables that agree on all entries observed before round $s$;
--   2. the decision takes the same value on any two tables that agree on all entries observed in all rounds.
--
--   This says that round $s$ is chosen from $\xi$ and the observations of earlier rounds only, and the decision from $\xi$ and the observations made. For a one-round tester the counts depend on $\xi$ alone.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition C.6, p.25

import Mathlib
import Definitions.Def_MetricMinTest_RoundTester_prefixCount
import Definitions.Def_MetricMinTest_RoundTester_totalCount

namespace MetricMinTest

/-- **Adaptedness of a round tester.** Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Definition C.6, p.25: the
count vector of round `s` is "a function of ξ and of the observations from rounds 1, …, s − 1",
and the decision "may depend on ξ and on all observations".

**Formalization Note.** (i) The counts of round `s` agree on any two tables that agree on the
entries read before round `s` (`ω i t` with `t < prefixCount s ξ ω i`); (ii) the decision agrees
on any two tables that agree on all entries read (`t < totalCount ξ ω i`). For a one-round tester
(i) says the counts depend on `ξ` only (Definition 4.4). -/
def RoundTester.IsAdapted {ι : Type} {q : ℕ} (T : RoundTester ι q) : Prop :=
  (∀ (s : Fin q) (ξ : T.Ξ) (ω ω' : ι → ℕ → ℝ),
      (∀ i t, t < T.prefixCount s ξ ω i → ω i t = ω' i t) → T.counts s ξ ω = T.counts s ξ ω') ∧
  (∀ (ξ : T.Ξ) (ω ω' : ι → ℕ → ℝ),
      (∀ i t, t < T.totalCount ξ ω i → ω i t = ω' i t) → T.accept ξ ω = T.accept ξ ω')

end MetricMinTest


