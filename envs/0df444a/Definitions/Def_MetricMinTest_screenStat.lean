-- Prove2me | Definitions.Def_MetricMinTest_screenStat
-- name    : MetricMinTest_screenStat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:03.743193+00:00
-- url     : https://prove2.me/theorems/d0726606-144f-461f-bfd0-51c9902ecd6a
-- title:
--   Screening statistic $S_z(t)$
-- statement:
--   For a target $z$, a threshold $r$ and $a_j=(\gamma-r-d(z,j))_+$,
--   $$S_z(t)=\sum_{s=1}^t\Big[a_{I_s}\big(X_s-r-d(z,I_s)\big)-\tfrac12a_{I_s}^2\Big].$$
--   One sample updates the statistics of all targets at once.
--
--   **Formalization Note** Draws are indexed from $0$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Lemma B.1, p.22

import Mathlib
import Definitions.Def_MetricMinTest_screenObs

namespace MetricMinTest

/-- **Screening statistic `S_z(t)`** (Lemma B.1). Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Lemma B.1, p.22:
`S_z(t) = ∑_{s=1}^t [a_{I_s}(X_s − r − d(z, I_s)) − a²_{I_s}/2]`, `aⱼ = (γ − r − d(z, j))₊`.

**Formalization Note.** Draws are indexed from `0` (`I 0, …, I (t−1)`), observations are
`screenObs`. -/
noncomputable def screenStat {ι : Type} [DecidableEq ι] (d : ι → ι → ℝ) (γ r : ℝ) (z : ι)
    (I : ℕ → ι) (ω : ι → ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ s ∈ Finset.range t,
    (max (γ - r - d z (I s)) 0 * (screenObs I ω s - r - d z (I s)) -
      (max (γ - r - d z (I s)) 0) ^ 2 / 2)

end MetricMinTest


