-- Prove2me | Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup
-- name    : EthierKurtz_IsStronglyContinuousContractionSemigroup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:41:20.203858+00:00
-- url     : https://prove2.me/theorems/1dcf5870-441a-4125-a52e-d519859518f3
-- title:
--   Strongly continuous contraction semigroup
-- statement:
--   A real-time operator family satisfying the semigroup law and contraction bound on nonnegative times, with identity at zero and strong right continuity at zero.
-- source:
--   Ethier and Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 1, pp. 6, 8.

import Mathlib

open Filter
open scoped Topology

namespace EthierKurtz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Chapter 1, p. 6. Only nonnegative times are used; negative-time values
of this real-indexed family are immaterial. Strong continuity is at zero from
strictly positive times, exactly as in the source. -/
def IsStronglyContinuousContractionSemigroup (T : ℝ → E →L[ℝ] E) : Prop :=
  T 0 = ContinuousLinearMap.id ℝ E ∧
  (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t)) ∧
  (∀ t : ℝ, 0 ≤ t → ‖T t‖ ≤ 1) ∧
  (∀ x : E, Tendsto (fun t : ℝ => T t x) (𝓝[>] (0 : ℝ)) (𝓝 x))

end EthierKurtz


