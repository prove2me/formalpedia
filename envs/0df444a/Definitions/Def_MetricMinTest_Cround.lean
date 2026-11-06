-- Prove2me | Definitions.Def_MetricMinTest_Cround
-- name    : MetricMinTest_Cround
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:11:42.311061+00:00
-- url     : https://prove2.me/theorems/d0bdc31d-e4a0-4227-b631-cec65de86341
-- title:
--   Optimal positive-instance expected cost of $q$-round testers
-- statement:
--   For $q$-round testers, the optimal positive-instance expected cost is
--   $$C^{(q)}_d(\gamma,\delta)=\inf_{\text{valid } q\text{-round testers}}\ \sup_{P\in\mathcal P_d^+(\gamma)}\mathbb E_P\tau,$$
--   the measure $C^\star$ of Definition 2.1 restricted to the testers of Definition C.6. Theorem A bounds it for $q=2$.
--
--   **Formalization Note** $\tau$ is the total number of queries. Infimum and supremum in $[0,\infty]$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition 2.1, p.6; Definition C.6, p.25; Theorem A, p.2

import Mathlib
import Definitions.Def_MetricMinTest_RoundTester_IsValid

namespace MetricMinTest

open MeasureTheory

/-- **Optimal positive-instance expected cost of `q`-round testers.** Chen–Fang, *Minimum-Mean
Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb):
the measure `C⋆` of Definition 2.1, p.6 ("the infimum, over valid testers, of
sup_{P ∈ P_d^+(γ)} E_P τ"), restricted to the `q`-round testers of Definition C.6, p.25. Theorem A
(p.2) calls the case `q = 2` "positive-instance expected cost" of two rounds.

**Formalization Note.** `τ` is the total number of queries (`RoundTester.cost`). Infimum and
supremum are in `ℝ≥0∞`; the infimum is `⊤` if no valid `q`-round tester exists. -/
noncomputable def Cround {ι : Type} [Fintype ι] (q : ℕ) (d : ι → ι → ℝ) (γ δ : ℝ) : ENNReal :=
  ⨅ (T : RoundTester ι q) (_ : T.IsValid d γ δ),
    ⨆ (P : Instance ι) (_ : IsPositive d γ P),
      ∫⁻ p, (T.cost p.1 p.2 : ENNReal) ∂(T.μξ.prod (streamLaw P))

end MetricMinTest


