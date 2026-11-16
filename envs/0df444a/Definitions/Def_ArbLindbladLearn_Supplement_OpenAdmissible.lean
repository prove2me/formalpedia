-- Prove2me | Definitions.Def_ArbLindbladLearn_Supplement_OpenAdmissible
-- name    : ArbLindbladLearn_Supplement_OpenAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:19:57.681952+00:00
-- url     : https://prove2.me/theorems/5f1a660e-c1e3-4198-96ab-ef8cb8c9ce84
-- title:
--   Admissible open-ended protocols
-- statement:
--   An open-ended protocol is **admissible** when it is physical and its control is measurable:
--   1. the initial state is a density operator, every duration is nonnegative, and every decision effect satisfies $0\le E_h\le1$;
--   2. the memory sizes, the durations, the instruments and the effects depend measurably on the history (on every finite history cylinder);
--   3. the stopping rule depends measurably on the history.
--
--   Conditions 1 and 2 are exactly those of the public bounded-query protocols; condition 3 is the one new field.
--
--   **Formalization Note** Measurability is what makes the success probabilities and expected evolution times the integrals of the actual Born laws.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), proof of Theorem 5.8, pp.46–48

import Mathlib
import Definitions.Def_ArbLindbladLearn_Supplement_OpenProtocol

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn.Supplement

open MeasureTheory
open LindbladTolerant.Testing

/-- Admissible open-ended protocols (proof of Theorem 5.8, pp.46–48, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…)): exactly the
conditions of the public `LindbladTolerant.Testing.Admissible` on the same control data (density
initial state, nonnegative durations, effects between `0` and `1`, measurable memory sizes,
durations, instrument base measures, instrument branches and effects on every finite history
cylinder), plus measurability of the stopping rule on every finite history cylinder.

**Formalization Note** The public conditions do not involve the query count, so they are taken
from `p.toProtocol 0`. Measurability is what makes the run probabilities and expected times
(`decisionProbability`, `expectedTime`) the integrals of the actual Born laws. -/
def OpenAdmissible {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (p : OpenProtocol n Ω) : Prop :=
  LindbladTolerant.Testing.Admissible (p.toProtocol 0) ∧
  ∀ r : ℕ, Measurable (fun h : Fin r → Ω => p.stop (List.ofFn h))

end ArbLindbladLearn.Supplement


