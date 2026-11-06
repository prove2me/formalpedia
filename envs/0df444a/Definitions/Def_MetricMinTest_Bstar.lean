-- Prove2me | Definitions.Def_MetricMinTest_Bstar
-- name    : MetricMinTest_Bstar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:10:37.368201+00:00
-- url     : https://prove2.me/theorems/9d3622ac-8171-4616-8995-553703711f51
-- title:
--   Optimal deterministic budget $B^\star_d(\gamma,\delta)$
-- statement:
--   $B^\star_d(\gamma,\delta)$ is the least integer $N$ for which some $(\gamma,\delta)$-valid sequential tester uses at most $N$ queries on every input and realization. Private randomization is allowed.
--
--   **Formalization Note** An infimum in $[0,\infty]$, equal to $\infty$ when no valid tester has a finite budget. "Every realization" is every private draw and every observation table.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition 2.1, p.6

import Mathlib
import Definitions.Def_MetricMinTest_Tester_IsValid

namespace MetricMinTest

/-- **Optimal deterministic budget `B⋆_d(γ, δ)`.** Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Definition 2.1, p.6:
"Let B⋆_d(γ, δ) be the least integer N for which a valid tester uses at most N queries on every
input and realization."

**Formalization Note.** An infimum in `ℝ≥0∞` over natural budgets `N`, equal to `⊤` when no valid
tester has a finite budget. "Every input and realization" is encoded as every private draw `ξ`
and every observation table `ω`. -/
noncomputable def Bstar {ι : Type} [DecidableEq ι] (d : ι → ι → ℝ) (γ δ : ℝ) : ENNReal :=
  ⨅ (N : ℕ) (_ : ∃ T : Tester ι, T.IsValid d γ δ ∧ ∀ ξ ω, T.stopTime ξ ω ≤ N), (N : ENNReal)

end MetricMinTest


