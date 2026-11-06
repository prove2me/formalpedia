-- Prove2me | Definitions.Def_MetricMinTest_oneStreamTime
-- name    : MetricMinTest_oneStreamTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:34.167869+00:00
-- url     : https://prove2.me/theorems/0d814e38-f951-44ac-81f1-8e086ca1dc75
-- title:
--   Crossing time $T=\inf\{n\ge1 : S_n\ge\beta\}$
-- statement:
--   For a boundary $\beta$, $T=\inf\{n\ge1 : S_n\ge\beta\}$, with $T=\infty$ if the boundary is never crossed. The one-stream test with cap $N$ passes if $T\le N$ and otherwise fails after $N$ samples.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §A.1, p.21

import Mathlib
import Definitions.Def_MetricMinTest_oneStreamStat

namespace MetricMinTest

/-- **Crossing time `T = inf {n ≥ 1 : S_n ≥ β}`** (Appendix A.1). Chen–Fang, *Minimum-Mean
Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §A.1,
p.21. "The test passes if T ≤ N and otherwise fails after N samples."

**Formalization Note.** Value in `ℕ∞`, `⊤` if the boundary is never crossed. -/
noncomputable def oneStreamTime (η a β : ℝ) (X : ℕ → ℝ) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : 1 ≤ n ∧ β ≤ oneStreamStat η a X n), (n : ℕ∞)

end MetricMinTest


