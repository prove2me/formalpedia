-- Prove2me | Definitions.Def_MetricMinTest_Cna
-- name    : MetricMinTest_Cna
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:11:02.832897+00:00
-- url     : https://prove2.me/theorems/915bd1ec-9729-4adc-b4b8-a2f74cdc63d1
-- title:
--   Optimal expected nonadaptive cost $C^{\mathrm{na}}_d(\gamma,\delta)$
-- statement:
--   $C^{\mathrm{na}}_d(\gamma,\delta)$ is the infimum of $\mathbb E_\xi N(\xi)$ over $(\gamma,\delta)$-valid nonadaptive testers. The cost of a nonadaptive tester does not depend on the instance.
--
--   **Formalization Note** Infimum in $[0,\infty]$ over valid one-round testers; $\infty$ if none exists.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition 4.4, p.9

import Mathlib
import Definitions.Def_MetricMinTest_RoundTester_IsValid
import Definitions.Def_MetricMinTest_RoundTester_naCost

namespace MetricMinTest

open MeasureTheory

/-- **Optimal expected nonadaptive cost `C^na_d(γ, δ)`.** Chen–Fang, *Minimum-Mean Testing under
Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Definition 4.4,
p.9: "let C^na_d(γ, δ) be the infimum of E_ξ N(ξ) over (γ, δ)-valid nonadaptive testers".

**Formalization Note.** Nonadaptive testers are one-round testers (`RoundTester ι 1`, Definition
C.6: "A one-round tester is nonadaptive in the sense of Definition 4.4"). The infimum is in
`ℝ≥0∞` and is `⊤` if no valid nonadaptive tester exists. -/
noncomputable def Cna {ι : Type} [Fintype ι] (d : ι → ι → ℝ) (γ δ : ℝ) : ENNReal :=
  ⨅ (T : RoundTester ι 1) (_ : T.IsValid d γ δ), ∫⁻ ξ, (T.naCost ξ : ENNReal) ∂T.μξ

end MetricMinTest


