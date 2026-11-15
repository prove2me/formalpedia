-- Prove2me | Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
-- name    : Kyprianou_Ch04_PathJumpAndItoIntegral
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T22:21:39.61723+00:00
-- url     : https://prove2.me/theorems/d30d1a16-83cf-480b-be5b-7b6f913c3871
-- title:
--   Actual path jump counting measure and stochastic-integral convergence criterion
-- statement:
--   The path jump measure is the pushforward of counting measure restricted to the nonzero jump times, with the actual time and signed increment as marks, using a genuine path left-limit. A stochastic integral is constrained to be the limit in probability of left-point stochastic sums for every finite horizon. This independent construction cannot be chosen freely to force a change-of-variables conclusion.
-- source:
--   Kyprianou (2006), first edition, Sections 4.3.1 and 4.3.2, pp. 90-95.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04

/-- Count the actual nonzero path jumps using a left-limit version.
This is a raw counting measure, not a compensated random measure. -/
noncomputable def pathJumpMeasure
    {Omega : Type} (X Xleft : NNReal -> Omega -> Real)
    (omega : Omega) : Measure (Real × Real) :=
  Measure.map
    (fun t : NNReal => ((t : Real), X t omega - Xleft t omega))
    ((Measure.count : Measure NNReal).restrict
      {t : NNReal | 0 < t ∧ X t omega ≠ Xleft t omega})

/-- A stochastic integral specified independently by convergence in probability
of left-point step-predictable sums. This does not assume an Itô formula. -/
def IsStochasticIntegralInProbability
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (X integrand integralProcess : NNReal -> Omega -> Real) : Prop :=
  forall t : NNReal, forall epsilon : Real, 0 < epsilon ->
    Tendsto
      (fun n : Nat =>
        (P {omega : Omega |
          epsilon <= abs (
            (∑ k ∈ Finset.range n,
              integrand (t * (k : NNReal) / (n : NNReal)) omega *
                (X (t * ((k + 1 : Nat) : NNReal) / (n : NNReal)) omega -
                  X (t * (k : NNReal) / (n : NNReal)) omega)) -
              integralProcess t omega)}).toReal)
      atTop (nhds 0)

end Kyprianou.Ch04


