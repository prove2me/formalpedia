-- Prove2me | Definitions.Def_MetricMinTest_Tester_stopTime
-- name    : MetricMinTest_Tester_stopTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:00.971932+00:00
-- url     : https://prove2.me/theorems/14991679-998c-4753-9ac2-201b6a2948ae
-- title:
--   Stopping time $\tau$ of a sequential tester
-- statement:
--   The stopping time $\tau$ is the first step $n$ at which the tester stops on its history of length $n$; it equals the number of queries made. If the tester never stops, $\tau=\infty$.
--
--   **Formalization Note** Valued in $\mathbb N\cup\{\infty\}$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §2, p.6

import Mathlib
import Definitions.Def_MetricMinTest_Tester_hist

namespace MetricMinTest

/-- **Stopping time `τ`** (number of queries). Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §2 p.6.

**Formalization Note.** `τ` is the first `n` at which `next` returns `none` on the history of
length `n`, so it equals the number of queries made; it is `⊤` if the tester never stops. -/
noncomputable def Tester.stopTime {ι : Type} [DecidableEq ι] (T : Tester ι) (ξ : T.Ξ)
    (ω : ι → ℕ → ℝ) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : T.next ξ (T.hist ξ ω n) = none), (n : ℕ∞)

end MetricMinTest


