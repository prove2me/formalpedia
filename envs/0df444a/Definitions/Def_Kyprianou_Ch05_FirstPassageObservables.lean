-- Prove2me | Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
-- name    : Kyprianou_Ch05_FirstPassageObservables
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T09:26:44.457776+00:00
-- url     : https://prove2.me/theorems/d04a9689-24cd-40b6-bfc6-dfe514379b51
-- title:
--   Strict first-passage observables, joint crossing law and renewal kernel
-- statement:
--   The actual extended strict crossing time; finite-time extraction with default used only on finite passage; exact overshoot X_tau-x, undershoot x-X_tau-, event-qualified joint law of positive overshoots, creeping probability, and the potential-jump kernel U(x-dy)Pi(y+du) for general measurable rectangles. No joint law or creeping theorem is assumed by these definitions.
-- source:
--   Kyprianou (2006), first edition, Section 5.2 (pp. 119-121), equation (5.7), and creeping Section 5.3 (pp.121-126).

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- The extended strict crossing time is finite only before death. -/
def PassageFinite
    {Omega : Type}
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (x : Real) (omega : Omega) : Prop :=
  strictUpcrossing Y death x omega ≠ ⊤

/-- Use the actual extended crossing time where finite, zero otherwise.
Only events of finite passage are used in passage laws. -/
noncomputable def passageFiniteTime
    {Omega : Type}
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (x : Real) (omega : Omega) : NNReal :=
  (strictUpcrossing Y death x omega).untopD 0

/-- Overshoot is X_(tau+) - x, evaluated only when tau is finite. -/
noncomputable def passageOvershoot
    {Omega : Type}
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (x : Real) (omega : Omega) : Real :=
  Y (passageFiniteTime Y death x omega) omega - x

/-- Undershoot is x - X_(tau+-), with a genuine path left limit. -/
noncomputable def passageUndershoot
    {Omega : Type}
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (x : Real) (omega : Omega) : Real :=
  x - Yleft (passageFiniteTime Y death x omega) omega

/-- Genuine two-variable jump-crossing law, excluding creeping.
The event contains an explicit positive overshoot, as in (5.7). -/
noncomputable def positiveJointPassageLaw
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (x : Real) (A B : Set Real) : ENNReal :=
  P {omega : Omega |
       PassageFinite Y death x omega ∧
       0 < passageOvershoot Y death x omega ∧
       passageOvershoot Y death x omega ∈ A ∧
       passageUndershoot Y Yleft death x omega ∈ B}

/-- Creeping includes the finite-crossing condition; a cemetery event
cannot be mistaken for an atom at the barrier. -/
noncomputable def creepingProbability
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (x : Real) : Real :=
  (P {omega : Omega |
      PassageFinite Y death x omega ∧
      passageOvershoot Y death x omega = 0}).toReal

/-- The right-hand side U(x-dy) Pi(y+du) on all measurable rectangles,
expressed in pre-jump position v and strictly crossing jump size z. -/
noncomputable def jumpPotentialKernel
    (U Pi : Measure Real)
    (x : Real) (A B : Set Real) : ENNReal := by
  classical
  exact ∫⁻ v in Set.Icc (0 : Real) x,
    (∫⁻ z in Set.Ioi (x-v),
      (if z - (x-v) ∈ A ∧ x-v ∈ B then
         (1 : ENNReal)
       else 0) ∂Pi) ∂U

end Kyprianou.Ch05


