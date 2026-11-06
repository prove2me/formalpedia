-- Prove2me | Definitions.Def_MetricMinTest_RoundTester_IsValid
-- name    : MetricMinTest_RoundTester_IsValid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:09:47.31199+00:00
-- url     : https://prove2.me/theorems/c3729b8d-d571-4ae4-9989-4b57949e41ec
-- title:
--   $(\gamma,\delta)$-validity of a round tester
-- statement:
--   A round tester is **$(\gamma,\delta)$-valid** for $d$ if it is a tester (its private law is a probability measure and it is adapted) and, for every instance $P\in\mathcal P_d$, $\Pr_P(\text{accept})\le\delta$ when some mean is negative and $\Pr_P(\text{accept})\ge1-\delta$ when $P\in\mathcal P_d^+(\gamma)$. Round testers always stop.
--
--   **Formalization Note** The acceptance set and the cost are required to be measurable for the product $\sigma$-algebra; probabilities are under $\mu_\xi\otimes$ (table law).
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition 2.1, p.6; Definitions 4.4 and C.6, pp.9, 25

import Mathlib
import Definitions.Def_MetricMinTest_RoundTester_IsAdapted
import Definitions.Def_MetricMinTest_RoundTester_cost
import Definitions.Def_MetricMinTest_IsPositive
import Definitions.Def_MetricMinTest_IsViolating
import Definitions.Def_MetricMinTest_streamLaw

namespace MetricMinTest

open MeasureTheory

/-- **`(γ, δ)`-validity of a round tester** (Definition 2.1 for the testers of Definitions 4.4
and C.6). Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission
(manuscript sha256 dcece193…ad32bb), Definition 2.1, p.6: "Pr_P(A = accept) ≤ δ if minᵢ µᵢ < 0,
Pr_P(A = accept) ≥ 1 − δ if P ∈ P_d^+(γ)".

**Formalization Note.** Validity bundles the conditions that make the object a tester at all:
`μξ` is a probability measure and the tester is adapted (`RoundTester.IsAdapted`). The acceptance
set and the cost are measurable for the product σ-algebra on `Ξ × (ι → ℕ → ℝ)`, which the
probabilities and expectations presuppose. Stopping is automatic (finitely many rounds, finite
counts). Error probabilities are over `μξ ⊗ streamLaw P`, for every `P ∈ P_d`. -/
def RoundTester.IsValid {ι : Type} [Fintype ι] {q : ℕ} (T : RoundTester ι q)
    (d : ι → ι → ℝ) (γ δ : ℝ) : Prop :=
  IsProbabilityMeasure T.μξ ∧ T.IsAdapted ∧
  MeasurableSet {p : T.Ξ × (ι → ℕ → ℝ) | T.accept p.1 p.2 = true} ∧
  Measurable (fun p : T.Ξ × (ι → ℕ → ℝ) => (T.cost p.1 p.2 : ENNReal)) ∧
  ∀ P : Instance ι, InClass d P →
    (IsViolating P →
      (T.μξ.prod (streamLaw P)) {p | T.accept p.1 p.2 = true} ≤ ENNReal.ofReal δ) ∧
    (IsPositive d γ P →
      ENNReal.ofReal (1 - δ) ≤ (T.μξ.prod (streamLaw P)) {p | T.accept p.1 p.2 = true})

end MetricMinTest


