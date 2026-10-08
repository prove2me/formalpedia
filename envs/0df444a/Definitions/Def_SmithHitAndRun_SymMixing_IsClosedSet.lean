-- Prove2me | Definitions.Def_SmithHitAndRun_SymMixing_IsClosedSet
-- name    : SmithHitAndRun_SymMixing_IsClosedSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:58:52.759959+00:00
-- url     : https://prove2.me/theorems/975312cd-66ef-4079-9a4d-a33414fbfa39
-- title:
--   Closed set for the one-step transition law
-- statement:
--   For a Markov transition law $P$ on $S$, a **closed set** is a nonempty measurable set $A\subseteq S$ that cannot be left in one step from any point it contains:
--   $$
--   A\ne\varnothing,\qquad P(x,A)=1\quad\text{for every }x\in A.
--   $$
--   Smith uses this notion to define indecomposability in Lemma 2 and in the nonperiodicity condition of Theorem 2. **Formalization Note** Measurability is explicit because $P(x,A)$ is a transition probability for measurable $A$.
-- source:
--   Smith, Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed over Bounded Regions, Oper. Res. 32(6) (1984), p. 1300, definition following Lemma 2

import Mathlib.Probability.Kernel.Basic

open MeasureTheory ProbabilityTheory

namespace SmithHitAndRun.SymMixing

/-- A measurable nonempty set that the chain cannot leave in one step from any of its points. -/
def IsClosedSet {α : Type*} [MeasurableSpace α] (P : Kernel α α) (A : Set α) : Prop :=
  A.Nonempty ∧ MeasurableSet A ∧ ∀ x ∈ A, P x A = 1

end SmithHitAndRun.SymMixing


