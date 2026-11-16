-- Prove2me | Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
-- name    : Kyprianou_Ch05_RiskConditionalPassage
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T09:40:13.023605+00:00
-- url     : https://prove2.me/theorems/42f5f82c-10dd-41c4-bbc0-42b3f1460de7
-- title:
--   Conditional joint first-passage measure and integrated-tail ladder jump law
-- statement:
--   Exact conditional joint overshoot/undershoot law with finite first passage and the positive integrated Levy-tail ascending record jump distribution, normalised by m. These are mathematical definitions, not assumptions about equality or limiting laws. The pre-passage running maximum is computed over all strictly earlier times, with a separate conditional risk drawdown law.
-- source:
--   Kyprianou (2006), Exercise 5.2, printed pp.133-134, author worked solution pp.322-323.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Conditional on a strictly finite passage, this is the exact
joint overshoot/undershoot law on measurable rectangles. -/
noncomputable def conditionalPassagePair
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (x : Real) (A B : Set Real) : Real :=
  let chance := (P {omega : Omega | PassageFinite Y death x omega}).toReal
  (P {omega : Omega |
       PassageFinite Y death x omega ∧
       passageOvershoot Y death x omega ∈ A ∧
       passageUndershoot Y Yleft death x omega ∈ B}).toReal / chance

/-- Ascending-record jump distribution in the negative-drift
spectrally positive risk model: F(dx)=nu((x,infinity))dx/m. -/
noncomputable def ascendingRecordJumpDistribution
    (nu : Measure Real) (m : Real) : Measure Real :=
  ((volume : Measure Real).restrict (Set.Ioi (0 : Real))).withDensity
    (fun x : Real => ENNReal.ofReal ((nu (Set.Ioi x)).toReal / m))


/-- Supremum of the risk process over all strictly pre-passage times.
For a cadlag path with finite positive passage this is the left limit
of its running supremum, rather than the left limit of Y itself. -/
noncomputable def runningSupremumBefore
    {Omega : Type} (Y : NNReal → Omega → Real)
    (t : NNReal) (omega : Omega) : Real :=
  sSup {z : Real | ∃ s : NNReal, s < t ∧ z = Y s omega}

/-- Conditional joint law of ruin overshoot and drawdown from the
historical running maximum immediately preceding the ruin jump. -/
noncomputable def conditionalRunningSupremumPair
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (x : Real) (A B : Set Real) : Real :=
  let chance :=
    (P {omega : Omega | PassageFinite Y death x omega}).toReal
  (P {omega : Omega |
       PassageFinite Y death x omega ∧
       passageOvershoot Y death x omega ∈ A ∧
       x - runningSupremumBefore Y
         (passageFiniteTime Y death x omega) omega ∈ B}).toReal / chance

end Kyprianou.Ch05


