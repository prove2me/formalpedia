-- Prove2me | Definitions.Def_MetricMinTest_Bround
-- name    : MetricMinTest_Bround
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:11:10.561645+00:00
-- url     : https://prove2.me/theorems/4269a8c6-f323-4658-9178-412a5eab5b5a
-- title:
--   Optimal deterministic budget of $q$-round testers
-- statement:
--   $B^{(q)}_d(\gamma,\delta)$ is the least $N$ for which some $(\gamma,\delta)$-valid $q$-round tester uses at most $N$ queries on every input and realization: the measure $B^\star$ of Definition 2.1 restricted to $q$-round testers.
--
--   **Formalization Note** "Every realization" is every private draw and every observation table. Infimum in $[0,\infty]$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition 2.1, p.6; Definition C.6, p.25

import Mathlib
import Definitions.Def_MetricMinTest_RoundTester_IsValid

namespace MetricMinTest

/-- **Optimal deterministic budget of `q`-round testers.** Chen–Fang, *Minimum-Mean Testing under
Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb): the measure `B⋆`
of Definition 2.1, p.6 ("the least integer N for which a valid tester uses at most N queries on
every input and realization"), restricted to the `q`-round testers of Definition C.6, p.25.

**Formalization Note.** "Every input and realization" is encoded as every private draw `ξ` and
every observation table `ω`. Infimum in `ℝ≥0∞`, `⊤` if no valid `q`-round tester has a uniform
budget. -/
noncomputable def Bround {ι : Type} [Fintype ι] (q : ℕ) (d : ι → ι → ℝ) (γ δ : ℝ) : ENNReal :=
  ⨅ (N : ℕ) (_ : ∃ T : RoundTester ι q, T.IsValid d γ δ ∧ ∀ ξ ω, T.cost ξ ω ≤ N), (N : ENNReal)

end MetricMinTest


