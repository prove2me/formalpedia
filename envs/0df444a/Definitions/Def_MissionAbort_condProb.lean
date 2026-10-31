-- Prove2me | Definitions.Def_MissionAbort_condProb
-- name    : MissionAbort_condProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:04.797348+00:00
-- url     : https://prove2.me/theorems/f7ce8a0f-a837-41de-bd30-27902a0bf316
-- title:
--   Conditional probability
-- statement:
--   The conditional probability $\mu(A\mid B)=\mu(A\cap B)/\mu(B)$.
--
--   **Formalization Note** At a null event $B$ the value is $0$. Every statement of this mission about a cost-to-go is guarded by positive probability of the history, and in the recursion a null event carries the factor $0$.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, Appendix A.2, p.EC.3

import Mathlib

namespace MissionAbort

open MeasureTheory

/-- The conditional probability `μ(A | B) = μ(A ∩ B)/μ(B)`.

**Formalization Note.** At a null `B` the value is Lean's `x/0 = 0`. Every statement of this mission
that asserts something about a cost-to-go guards the history by positive probability under the law
in question, and a null term `μ(Yₙ₊₁ = k | y)` in the recursion multiplies a value by `0`. -/
noncomputable def condProb {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A B : Set Ω) : ℝ :=
  μ.real (A ∩ B) / μ.real B

end MissionAbort


