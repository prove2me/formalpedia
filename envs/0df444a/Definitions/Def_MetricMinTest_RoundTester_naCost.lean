-- Prove2me | Definitions.Def_MetricMinTest_RoundTester_naCost
-- name    : MetricMinTest_RoundTester_naCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:13.862973+00:00
-- url     : https://prove2.me/theorems/da1b9655-b23e-45a8-941a-49960d296684
-- title:
--   Query count $N(\xi)$ of a nonadaptive tester
-- statement:
--   For a nonadaptive (one-round) tester, $N(\xi)=\sum_j n_j(\xi)$ is its total number of queries given the private draw $\xi$.
--
--   **Formalization Note** For an adapted one-round tester the counts do not depend on the observations, so $N(\xi)$ is the cost evaluated at the all-zero table.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition 4.4, p.9

import Mathlib
import Definitions.Def_MetricMinTest_RoundTester_cost

namespace MetricMinTest

/-- **Query count `N(ξ)` of a nonadaptive tester** (Definition 4.4). Chen–Fang, *Minimum-Mean
Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb),
Definition 4.4, p.9: "Write N(ξ) = ∑ⱼ nⱼ(ξ)".

**Formalization Note.** For a one-round tester that is adapted, the counts do not depend on the
table, so `N(ξ)` is the cost evaluated at the all-zero table. -/
def RoundTester.naCost {ι : Type} [Fintype ι] (T : RoundTester ι 1) (ξ : T.Ξ) : ℕ :=
  T.cost ξ (fun _ _ => 0)

end MetricMinTest


