-- Prove2me | Definitions.Def_MetricMinTest_RoundTester_totalCount
-- name    : MetricMinTest_RoundTester_totalCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:39.609495+00:00
-- url     : https://prove2.me/theorems/412cfe50-9ce0-4146-b50d-b028ca9edf31
-- title:
--   Total query count $N_i$ at an index
-- statement:
--   The total number of queries to index $i$ is $N_i=\sum_s n^{(s)}_i$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §2, p.6; Definition C.6, p.25

import Mathlib
import Definitions.Def_MetricMinTest_RoundTester

namespace MetricMinTest

/-- **Total number of queries to index `i`**, `Nᵢ = ∑_s n^(s)_i`. Chen–Fang, *Minimum-Mean
Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §2
p.6 ("Write Nᵢ for its query count at index i") and Definition C.6, p.25. -/
def RoundTester.totalCount {ι : Type} {q : ℕ} (T : RoundTester ι q) (ξ : T.Ξ)
    (ω : ι → ℕ → ℝ) (i : ι) : ℕ :=
  ∑ s, T.counts s ξ ω i

end MetricMinTest


