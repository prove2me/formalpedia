-- Prove2me | Definitions.Def_MetricMinTest_Bna
-- name    : MetricMinTest_Bna
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:10:56.470581+00:00
-- url     : https://prove2.me/theorems/ed7ea7a3-164d-4938-997b-d36c22bb6a68
-- title:
--   Optimal nonadaptive budget $B^{\mathrm{na}}_d(\gamma,\delta)$
-- statement:
--   $B^{\mathrm{na}}_d(\gamma,\delta)$ is the least $N$ for which some $(\gamma,\delta)$-valid nonadaptive tester satisfies $N(\xi)\le N$ for every $\xi$.
--
--   **Formalization Note** Infimum in $[0,\infty]$ over natural budgets.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition 4.4, p.9

import Mathlib
import Definitions.Def_MetricMinTest_RoundTester_IsValid
import Definitions.Def_MetricMinTest_RoundTester_naCost

namespace MetricMinTest

/-- **Optimal nonadaptive budget `B^na_d(γ, δ)`.** Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Definition 4.4, p.9: "Let
B^na_d(γ, δ) be the least N for which some (γ, δ)-valid nonadaptive tester satisfies N(ξ) ≤ N for
every ξ".

**Formalization Note.** An infimum in `ℝ≥0∞` over natural `N`; `⊤` if no valid nonadaptive
tester has a uniform budget. Nonadaptive testers are `RoundTester ι 1`. -/
noncomputable def Bna {ι : Type} [Fintype ι] (d : ι → ι → ℝ) (γ δ : ℝ) : ENNReal :=
  ⨅ (N : ℕ) (_ : ∃ T : RoundTester ι 1, T.IsValid d γ δ ∧ ∀ ξ, T.naCost ξ ≤ N), (N : ENNReal)

end MetricMinTest


