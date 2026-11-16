-- Prove2me | Definitions.Def_Kyprianou_Ch06_certificate_exercise_6_7
-- name    : Kyprianou_Ch06_certificate_exercise_6_7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:27:07.453393+00:00
-- url     : https://prove2.me/theorems/eb05d519-6550-4519-88c0-9f152fd68c86
-- title:
--   Full quantified certificate for exercise:6.7
-- statement:
--   Exact fully quantified source theorem/exercise as a Prop, generated from the authoritative live theorem telescope and target with no conclusion weakening.
-- source:
--   Kyprianou (2006), Exercise 6.7(i)–(ii), printed pp. 176–177; physical PDF pp. 93–94.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Closed, full quantified source proposition from secondWienerHopfFactorisationIdentity. -/
def certificate_exercise_6_7 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (L : NNReal → Omega → NNReal)
    (F : NNReal → MeasurableSpace Omega)
    (expTime : Real → Omega → NNReal)
    (kappa : Real → Real → Real)
    (hX : IsRealLevyProcess P X)
    (hNotSubordinator : ¬ IsSubordinatorProcess P X)
    (hL : IsAdmissibleLocalTimeAtMaximum P F X L)
    (hExpTime : ∀ (alpha : Real), 0 < alpha →
      ∀ t : NNReal,
        P {omega | t < expTime alpha omega} =
          ENNReal.ofReal (Real.exp (-alpha * (t : Real))))
    (hExpIndependent : ∀ alpha : Real, 0 < alpha →
      ∀ (m : Nat) (times : Fin m → NNReal)
        (A : Fin m → Set Real) (B : Set NNReal),
        (∀ i, MeasurableSet (A i)) → MeasurableSet B →
        P {omega | expTime alpha omega ∈ B ∧
          (∀ i : Fin m, X (times i) omega ∈ A i)} =
            P {omega | expTime alpha omega ∈ B} *
            P {omega |
              ∀ i : Fin m, X (times i) omega ∈ A i})
    (hKappa : ∀ (alpha beta : Real), 0 ≤ alpha → 0 ≤ beta →
      ∀ t : NNReal,
        (∫ omega,
          let tau := inverseLocalTime L t omega
          if tau = ⊤ then (0 : Real)
          else Real.exp (-alpha * (↑(tau.untopD 0) : Real) -
            beta * runningMaximum X (tau.untopD 0) omega) ∂P) =
        Real.exp (-(t : Real) * kappa alpha beta)),
    (∀ (alpha beta x : Real), 0 < alpha → 0 ≤ beta →
      (∫ omega,
        let tau := firstEntranceTime X 0 (Set.Ioi x) omega
        if tau = ⊤ then (0 : Real)
        else Real.exp (-alpha * (↑(tau.untopD 0) : Real) -
          beta * X (tau.untopD 0) omega) ∂P) =
      (∫ omega,
        if x < runningMaximum X (expTime alpha omega) omega
        then Real.exp (-beta *
          runningMaximum X (expTime alpha omega) omega)
        else (0 : Real) ∂P) /
      (∫ omega,
        Real.exp (-beta *
          runningMaximum X (expTime alpha omega) omega) ∂P)) ∧
    (∀ (alpha beta q : Real),
      0 < alpha → 0 ≤ beta → 0 < q →
      kappa alpha q ≠ 0 →
      (q = beta →
        DifferentiableAt Real (fun u => kappa alpha u) beta) ∧
      (∫ x in Set.Ioi (0 : Real),
        Real.exp (-q * x) *
          (∫ omega,
            let tau := firstEntranceTime X 0 (Set.Ioi x) omega
            if tau = ⊤ then (0 : Real)
            else Real.exp (-alpha * (↑(tau.untopD 0) : Real) -
              beta * (X (tau.untopD 0) omega - x)) ∂P) ∂volume) =
      (if q = beta then
        deriv (fun u => kappa alpha u) beta /
          kappa alpha beta
      else
        (kappa alpha q - kappa alpha beta) /
          ((q - beta) * kappa alpha q)))

end Kyprianou.Ch06


