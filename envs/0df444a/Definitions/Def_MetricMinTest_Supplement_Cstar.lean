-- Prove2me | Definitions.Def_MetricMinTest_Supplement_Cstar
-- name    : MetricMinTest_Supplement_Cstar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:24:54.428186+00:00
-- url     : https://prove2.me/theorems/03998aa6-6634-473e-ac9d-2056949ef89b
-- title:
--   Optimal positive-instance expected cost $C^\star_d(\gamma,\delta)$
-- statement:
--   For a finite metric or pseudometric $d$ and $\gamma,\delta\in(0,1/4]$, the **optimal expected cost** is
--   $$C^\star_d(\gamma,\delta)=\inf_{T\ (\gamma,\delta)\text{-valid}}\ \sup_{P\in\mathcal P_d^+(\gamma)}\mathbb E_P\,\tau ,$$
--   the infimum over all $(\gamma,\delta)$-valid sequential testers (Definition 2.1) of the worst-case expected number of queries on positive instances.
--
--   It is the adaptive expected-cost complexity measure of the paper, next to the deterministic budget $B^\star_d(\gamma,\delta)$, and $C^\star_d\le B^\star_d$.
--
--   **Formalization Note** The tester class is the published one (privately randomized sequential testers in the stack-of-streams observation model, validity including measurability); infimum, supremum and expectation are in $[0,\infty]$, and $C^\star_d=\infty$ if no valid tester exists.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition 2.1, p.6

import Mathlib
import Definitions.Def_MetricMinTest_Tester_IsValid

namespace MetricMinTest.Supplement

open MeasureTheory

/-- **Optimal positive-instance expected cost `C⋆_d(γ, δ)`** (Definition 2.1). Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb),
Definition 2.1, p.6: "Let C⋆_d(γ, δ) be the infimum, over valid testers, of
sup_{P ∈ P_d^+(γ)} E_P τ."

**Formalization Note.** Same tester class as the published `Bstar`: privately randomized
sequential testers (`Tester`) that are `(γ, δ)`-valid (`Tester.IsValid`). `E_P τ` is the
`ℝ≥0∞` integral of the stopping time under `μξ ⊗ streamLaw P`. The infimum and the supremum are
in `ℝ≥0∞`; the infimum is `⊤` if no valid tester exists. -/
noncomputable def Cstar {ι : Type} [DecidableEq ι] (d : ι → ι → ℝ) (γ δ : ℝ) : ENNReal :=
  ⨅ (T : Tester ι) (_ : T.IsValid d γ δ),
    ⨆ (P : Instance ι) (_ : IsPositive d γ P),
      ∫⁻ p, ((T.stopTime p.1 p.2 : ℕ∞) : ENNReal) ∂(T.μξ.prod (streamLaw P))

end MetricMinTest.Supplement


