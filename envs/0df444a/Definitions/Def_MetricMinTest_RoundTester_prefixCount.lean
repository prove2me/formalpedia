-- Prove2me | Definitions.Def_MetricMinTest_RoundTester_prefixCount
-- name    : MetricMinTest_RoundTester_prefixCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:42.019245+00:00
-- url     : https://prove2.me/theorems/fa02931b-fe41-4280-ba3d-c18cc5261dc7
-- title:
--   Queries to an index before round $s$
-- statement:
--   For a round tester, the number of queries to index $i$ before round $s$ is $\sum_{s'<s}n^{(s')}_i$. Round $s$ reads the next $n^{(s)}_i$ entries of the stream of $i$ after these.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition C.6, p.25

import Mathlib
import Definitions.Def_MetricMinTest_RoundTester

namespace MetricMinTest

/-- **Queries to index `i` before round `s`**, `∑_{s' < s} n^(s')_i`. Chen–Fang, *Minimum-Mean
Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb),
Definition C.6, p.25. Round `s` reads the stream entries `ω i t` with
`prefixCount s ≤ t < prefixCount s + n^(s)_i`. -/
def RoundTester.prefixCount {ι : Type} {q : ℕ} (T : RoundTester ι q) (s : Fin q) (ξ : T.Ξ)
    (ω : ι → ℕ → ℝ) (i : ι) : ℕ :=
  ∑ s' ∈ Finset.univ.filter (fun s' : Fin q => s' < s), T.counts s' ξ ω i

end MetricMinTest


