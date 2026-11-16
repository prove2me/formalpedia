-- Prove2me | Definitions.Def_Kyprianou_Ch05_ExponentialPassageMoments
-- name    : Kyprianou_Ch05_ExponentialPassageMoments
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T09:28:26.325189+00:00
-- url     : https://prove2.me/theorems/19f7aa79-e8d3-4a2a-b917-179936ee7548
-- title:
--   Full exponential-time, overshoot, creeping and joint first-passage moments
-- statement:
--   Measurable finite strict-passage expectations with real exponential killing/overshoot/creeping and joint undershoot laws, and zero on infinite passage. These introduce observables only and assume no desired transform identities.
-- source:
--   Kyprianou (2006), Exercises 5.5 and 5.7, first edition, pp.135-137.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Finite strict passage with the full exponential-time discount and
Laplace factor, with infinity contributing zero. -/
noncomputable def exponentialFirstPassageMoment
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (alpha beta x : Real) : Real := by
  classical
  exact ∫ omega : Omega,
    if PassageFinite Y death x omega then
      Real.exp (-alpha * (passageFiniteTime Y death x omega : Real) -
                beta * Y (passageFiniteTime Y death x omega) omega)
    else 0 ∂P

/-- Exponential discount of the overshoot; no landing at infinity. -/
noncomputable def exponentialOvershootMoment
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (alpha beta x : Real) : Real := by
  classical
  exact ∫ omega : Omega,
    if PassageFinite Y death x omega then
      Real.exp (-alpha * (passageFiniteTime Y death x omega : Real) -
                beta * passageOvershoot Y death x omega)
    else 0 ∂P

/-- Exponentially discounted finite creeping probability. -/
noncomputable def exponentialCreepingMoment
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (alpha x : Real) : Real := by
  classical
  exact ∫ omega : Omega,
    if PassageFinite Y death x omega ∧
       passageOvershoot Y death x omega = 0 then
      Real.exp (-alpha * (passageFiniteTime Y death x omega : Real))
    else 0 ∂P

/-- Both first-passage values in the joint exponent; the source's
part (i) excludes creeping but part (ii) includes it. -/
noncomputable def jointFirstPassageMoment
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (beta gamma x : Real) (jumpOnly : Bool) : Real := by
  classical
  exact ∫ omega : Omega,
    if PassageFinite Y death x omega ∧
       (jumpOnly = false ∨ 0 < passageOvershoot Y death x omega) then
      Real.exp
        (-beta * Yleft (passageFiniteTime Y death x omega) omega -
         gamma * passageOvershoot Y death x omega)
    else 0 ∂P

end Kyprianou.Ch05


