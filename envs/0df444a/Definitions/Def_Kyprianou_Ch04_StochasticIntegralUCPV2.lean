-- Prove2me | Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
-- name    : Kyprianou_Ch04_StochasticIntegralUCPV2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T10:15:38.355079+00:00
-- url     : https://prove2.me/theorems/2fcb5557-113e-41ce-a4e8-b6b34d582220
-- title:
--   Correct uniform-on-compact stochastic integral convergence criterion (review v2)
-- statement:
--   The raw path-jump counting measure uses actual càdlàg left-limit increments. The stochastic integral is separately specified by left-point partitions of a fixed finite horizon, stopped at each t. The error exceeds epsilon at some t in the horizon with probability tending to zero, giving uniform convergence in probability on compact time intervals.
-- source:
--   Kyprianou (2006), first edition, Sections 4.3.1 and 4.3.2, pp. 90-95.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
namespace Kyprianou.Ch04
def IsStochasticIntegralInProbabilityV2
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (X integrand integralProcess : NNReal -> Omega -> Real) : Prop :=
  ∀ T : NNReal, ∀ epsilon : Real, 0 < epsilon →
    Tendsto
      (fun n : Nat =>
        (P {omega : Omega |
          ∃ t : NNReal, t ≤ T ∧
            epsilon ≤ abs (
              (∑ k ∈ Finset.range n,
                let u : NNReal := T * (k : NNReal) / (n : NNReal)
                let v : NNReal := T * ((k + 1 : Nat) : NNReal) / (n : NNReal)
                integrand u omega *
                  (X (min t v) omega - X (min t u) omega)) -
              integralProcess t omega)}).toReal)
      atTop (nhds 0)

end Kyprianou.Ch04


