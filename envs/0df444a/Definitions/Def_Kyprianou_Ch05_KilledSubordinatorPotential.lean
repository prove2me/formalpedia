-- Prove2me | Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
-- name    : Kyprianou_Ch05_KilledSubordinatorPotential
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T09:26:12.505137+00:00
-- url     : https://prove2.me/theorems/547a66e3-c6af-404e-9dba-c73f3376bd1d
-- title:
--   Killed subordinators, cemetery, strict passage and q-potential measures
-- statement:
--   Living real subordinator Y with independent killing at eta>=0, explicit cemetery Option state, strict pre-death first passage, genuine left-limit version, exact discounted occupation identities U^(q), and the killed Laplace exponent eta+d*theta+integral(1-exp(-theta*x))Pi(dx). This intentionally treats existence of a compatible potential family as a separate construction/proof interface.
-- source:
--   Kyprianou (2006), first edition, Chapter 5, Section 5.1, printed pp. 111-113, equation (5.1); strict passage and left limits pp. 116-121.

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- A real-valued subordinator killed at an independent exponential time,
where zero killing means the death time is literally infinite. -/
def IsKilledSubordinator
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta : Real) : Prop :=
  Kyprianou.Ch03.IsSubordinator P Y ∧
  0 ≤ eta ∧
  Measurable death ∧
  (eta = 0 → ∀ omega : Omega, death omega = ⊤) ∧
  (∀ t : NNReal,
     P {omega : Omega |
         (t : WithTop NNReal) < death omega} =
       ENNReal.ofReal (Real.exp (-eta * (t : Real)))) ∧
  Indep
    (MeasurableSpace.comap death inferInstance)
    (MeasurableSpace.comap
      (fun omega : Omega => fun t : NNReal => Y t omega)
      inferInstance) P

/-- The cemetery is a distinct None value: no zero/real-valued surrogate. -/
noncomputable def killedValue
    {Omega : Type} (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (t : NNReal) (omega : Omega) : Option Real :=
  if (t : WithTop NNReal) < death omega then some (Y t omega) else none

/-- First strict upcrossing before the cemetery transition, with +infinity
when there is no living strict crossing. -/
noncomputable def strictUpcrossing
    {Omega : Type} (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (x : Real) (omega : Omega) : WithTop NNReal :=
  sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
    {t : NNReal | 0 < t ∧
      (t : WithTop NNReal) < death omega ∧ x < Y t omega})

/-- A specified left-limit version, without assuming the jump compensation law. -/
def IsLeftLimitVersion
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (Y Yleft : NNReal → Omega → Real) : Prop :=
  ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t →
    Tendsto (fun s : NNReal => Y s omega)
      (nhdsWithin t (Set.Iio t)) (nhds (Yleft t omega))

/-- Exact discounted expected occupation measure of the living path. -/
def IsKilledPotential
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (q : Real) (Uq : Measure Real) : Prop :=
  0 ≤ q ∧
  ∀ B : Set Real, MeasurableSet B →
    Uq B =
      ∫⁻ t in Set.Ici (0 : Real),
        ENNReal.ofReal (Real.exp (-q * t)) *
        P {omega : Omega |
          (Real.toNNReal t : WithTop NNReal) < death omega ∧
          Y (Real.toNNReal t) omega ∈ B} ∂volume

/-- A q-potential family, including the undiscounted q=0 measure. -/
def IsKilledPotentialFamily
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (U : Real → Measure Real) : Prop :=
  ∀ q : Real, 0 ≤ q → IsKilledPotential P Y death q (U q)

/-- The killed Laplace triplet with killing, nonnegative drift and a
positive-jump finite-variation Levy measure, source equation (5.1). -/
def IsKilledLaplaceTriplet
    (eta d : Real) (Pi : Measure Real)
    (Phi : Real → Real) : Prop :=
  0 ≤ eta ∧ 0 ≤ d ∧ Pi (Set.Iic (0 : Real)) = 0 ∧
  (∫⁻ x in Set.Ioi (0 : Real),
    ENNReal.ofReal (min (1 : Real) x) ∂Pi) < ⊤ ∧
  ∀ theta : Real, 0 ≤ theta →
    Phi theta = eta + d * theta +
      ∫ x in Set.Ioi (0 : Real),
        (1 - Real.exp (-theta * x)) ∂Pi

end Kyprianou.Ch05


