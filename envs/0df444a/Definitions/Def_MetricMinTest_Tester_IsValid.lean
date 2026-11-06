-- Prove2me | Definitions.Def_MetricMinTest_Tester_IsValid
-- name    : MetricMinTest_Tester_IsValid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:09:16.452341+00:00
-- url     : https://prove2.me/theorems/89fcd6b2-c963-46a5-9c05-cef047a4ba04
-- title:
--   $(\gamma,\delta)$-validity of a sequential tester
-- statement:
--   A sequential tester is **$(\gamma,\delta)$-valid** for $d$ if, for every instance $P\in\mathcal P_d$,
--   1. it stops almost surely;
--   2. $\Pr_P(A=\text{accept})\le\delta$ if $\min_i\mu_i<0$;
--   3. $\Pr_P(A=\text{accept})\ge1-\delta$ if $P\in\mathcal P_d^+(\gamma)$.
--
--   Probabilities are over the whole experiment: the private randomness and the observations, for a fixed instance.
--
--   **Formalization Note** The experiment's law is $\mu_\xi\otimes$ (table law). Validity also requires that $\mu_\xi$ is a probability measure and that the acceptance event and the stopping time are measurable, which the paper's probabilities and expectations presuppose.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition 2.1, p.6

import Mathlib
import Definitions.Def_MetricMinTest_Tester_stopTime
import Definitions.Def_MetricMinTest_Tester_Accepts
import Definitions.Def_MetricMinTest_IsPositive
import Definitions.Def_MetricMinTest_IsViolating
import Definitions.Def_MetricMinTest_streamLaw

namespace MetricMinTest

open MeasureTheory

/-- **`(γ, δ)`-validity of a sequential tester** (Definition 2.1). Chen–Fang, *Minimum-Mean
Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb),
Definition 2.1, p.6: "A tester is (γ, δ)-valid if it stops almost surely on every P ∈ P_d and
Pr_P(A = accept) ≤ δ if minᵢ µᵢ < 0, Pr_P(A = accept) ≥ 1 − δ if P ∈ P_d^+(γ)."

**Formalization Note.** Probabilities are over the whole experiment, the product of the private
randomness `μξ` (required to be a probability measure) and the observation table `streamLaw P`.
The acceptance event and the stopping time are required to be measurable for the product
σ-algebra, which the paper's probabilities and expectations presuppose. The conditions are
imposed for every `P ∈ P_d` (every law on `[−1, 1]`); instances that are neither violating nor
positive are unconstrained. -/
def Tester.IsValid {ι : Type} [DecidableEq ι] (T : Tester ι) (d : ι → ι → ℝ) (γ δ : ℝ) : Prop :=
  IsProbabilityMeasure T.μξ ∧
  MeasurableSet {p : T.Ξ × (ι → ℕ → ℝ) | T.Accepts p.1 p.2} ∧
  Measurable (fun p : T.Ξ × (ι → ℕ → ℝ) => ((T.stopTime p.1 p.2 : ℕ∞) : ENNReal)) ∧
  ∀ P : Instance ι, InClass d P →
    (T.μξ.prod (streamLaw P)) {p | T.stopTime p.1 p.2 = ⊤} = 0 ∧
    (IsViolating P →
      (T.μξ.prod (streamLaw P)) {p | T.Accepts p.1 p.2} ≤ ENNReal.ofReal δ) ∧
    (IsPositive d γ P →
      ENNReal.ofReal (1 - δ) ≤ (T.μξ.prod (streamLaw P)) {p | T.Accepts p.1 p.2})

end MetricMinTest


