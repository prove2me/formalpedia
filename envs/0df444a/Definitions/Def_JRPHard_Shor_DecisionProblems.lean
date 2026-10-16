-- Prove2me | Definitions.Def_JRPHard_Shor_DecisionProblems
-- name    : JRPHard_Shor_DecisionProblems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T12:37:58.190109+00:00
-- url     : https://prove2.me/theorems/3225e86b-22cf-4255-84b6-e075538efa66
-- title:
--   Partition decision predicate (RangeDivisor predicates imported from the shared JRPHard.RangeDiv.Setting)
-- statement:
--   A **Partition** yes instance is a finite indexed list $(a_i)_{i=1}^n$ for which some set of indices $S$ has twice its subtotal equal to the total:
--   $$2\sum_{i\in S}a_i=\sum_{i=1}^n a_i.$$
--   This predicate is the Partition question of the Appendix reduction; the RangeDivisor instance condition ($0<L\le U\le M$, $L+U<2\sqrt{2LU}$) and its yes-instances (a divisor of $M$ in $[L,U]$), p. 12, are the shared definitions `JRPHard.RangeDiv.IsRangeDivisorInstance` and `JRPHard.RangeDiv.HasDivisorIn`, imported here. Positivity and the bit range of the particular Partition inputs are imposed by the reduction theorems.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 12 and 16, RangeDivisor definition and Appendix, Partition definition

import Mathlib
import Definitions.Def_JRPHard_RangeDiv_Setting

namespace JRPHard.Shor

open Finset

/-- The listed positive integers can be partitioned into two equal sum parts. -/
def PartitionYes {n : ℕ} (a : Fin n → ℕ) : Prop :=
  ∃ S : Finset (Fin n), 2 * ∑ i ∈ S, a i = ∑ i, a i

end JRPHard.Shor


