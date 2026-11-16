-- Prove2me | Definitions.Def_Kyprianou_Ch05_BivariateKilledSubordinator
-- name    : Kyprianou_Ch05_BivariateKilledSubordinator
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T09:29:29.538625+00:00
-- url     : https://prove2.me/theorems/dee2489d-eb6b-4e74-8239-2078370344fa
-- title:
--   Dependent bivariate killed subordinators and actual joint potential/kernel
-- statement:
--   Joint killed-subordinator Laplace transform with arbitrary dependence and a truly bivariate Levy jump measure, independent exponential cemetery time, exact bivariate occupation renewal measure, and full four-coordinate jump compensation kernel. No quadruple passage equality is assumed.
-- source:
--   Kyprianou (2006) Exercise 5.4, pp.134-135, worked solution pp.324-325.

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Bivariate killed subordinator law, with a joint jump measure and
joint exponent: dependence between X and Y is unrestricted. The killing
time is independent of the whole bivariate path. -/
def IsKilledBivariateSubordinator
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta dX dY : Real)
    (Pi : Measure (Real × Real)) : Prop :=
  Kyprianou.Ch03.IsSubordinator P X ∧
  Kyprianou.Ch03.IsSubordinator P Y ∧
  0 ≤ eta ∧ 0 ≤ dX ∧ 0 ≤ dY ∧
  Measurable death ∧
  (eta = 0 → ∀ omega : Omega, death omega = ⊤) ∧
  (∀ t : NNReal,
     P {omega : Omega | (t : WithTop NNReal) < death omega} =
       ENNReal.ofReal (Real.exp (-eta*(t : Real)))) ∧
  Indep
    (MeasurableSpace.comap death inferInstance)
    (MeasurableSpace.comap
      (fun omega : Omega =>
         fun t : NNReal => (X t omega,Y t omega)) inferInstance) P ∧
  Pi ((Set.Ici (0 : Real)).prod (Set.Ici (0 : Real)))ᶜ = 0 ∧
  (∫⁻ z : Real × Real,
     ENNReal.ofReal (min (1 : Real) (z.1+z.2)) ∂Pi) < ⊤ ∧
  ∀ (t : NNReal) (a b : Real), 0 ≤ a → 0 ≤ b →
    (∫ omega, Real.exp (-a*X t omega-b*Y t omega) ∂P) =
      Real.exp (-(t : Real)*
        (dX*a+dY*b+
          ∫ z : Real × Real,
             (1-Real.exp (-a*z.1-b*z.2)) ∂Pi))

/-- Undiscounted joint renewal measure U(ds,dz) from the actual
alive-path occupation of (X,Y), with no independence assumption. -/
def IsBivariateKilledPotential
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (X Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (U : Measure (Real × Real)) : Prop :=
  ∀ B : Set (Real × Real), MeasurableSet B →
    U B = ∫⁻ t in Set.Ici (0 : Real),
       P {omega : Omega |
          (Real.toNNReal t : WithTop NNReal) < death omega ∧
          (X (Real.toNNReal t) omega,Y (Real.toNNReal t) omega) ∈ B} ∂volume

/-- Quadruple law's bivariate compensator kernel, tracking
Delta X, X_{tau-}, x-Y_{tau-}, Y_tau-x respectively. -/
noncomputable def bivariateQuadrupleKernel
    (U Pi : Measure (Real × Real)) (x : Real)
    (T S B A : Set Real) : ENNReal := by
  classical
  exact ∫⁻ pre : Real × Real,
    ∫⁻ jump : Real × Real,
      (if jump.1 ∈ T ∧ pre.1 ∈ S ∧
        x-pre.2 ∈ B ∧ pre.2+jump.2-x ∈ A ∧
        pre.2 ≤ x ∧ x < pre.2+jump.2
       then (1 : ENNReal) else 0) ∂Pi ∂U

end Kyprianou.Ch05


