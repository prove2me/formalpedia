-- Prove2me | Definitions.Def_Kyprianou_Ch07_certificate_exercise_7_1
-- name    : Kyprianou_Ch07_certificate_exercise_7_1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T15:04:38.690975+00:00
-- url     : https://prove2.me/theorems/221e6884-f11c-4873-8d61-c56aa7826113
-- title:
--   Full quantified certificate for exercise7_1SupremumMomentsAllParts
-- statement:
--   Full quantified source proposition of Kyprianou.Ch07.exercise7_1SupremumMomentsAllParts with source-fidelity repairs; every binder and clause is retained.
-- source:
--   Kyprianou (2006), Exercise 7.1(i)–(iii) and (7.31), printed pp.206–207, original PDF pp.215–216, Windows Ky.pdf sheet 108.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
open MeasureTheory Filter Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Source-quantified full proposition of exercise7_1SupremumMomentsAllParts. -/
def certificate_exercise_7_1 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (XK : Real → NNReal → Omega → Real)
    (e : Real → Omega → NNReal)
    (Pi : Measure Real) (b : Real) (sigma2 : NNReal)
    (PiK : Real → Measure Real) (bK : Real → Real)
    (FK : Real → NNReal → MeasurableSpace Omega)
    (Ldown : Real → NNReal → Omega → NNReal)
    (n : Nat) (hn : 1 ≤ n)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi)
    (hMoment : (∫⁻ x : Real in Set.Ioi 1,
       ENNReal.ofReal (x ^ n) ∂Pi) < ⊤)
    (hPiK : ∀ K : Real, 0 < K → ∀ B : Set Real, MeasurableSet B →
       PiK K B =
          Pi (B ∩ Set.Ioi (-K)) +
          (if -K ∈ B then Pi (Set.Iic (-K)) else 0))
    (hXK : ∀ K : Real, 0 < K →
       Kyprianou.Ch06.IsRealLevyProcess P (XK K) ∧
       Kyprianou.Ch06.IsLevyKhintchineTriplet
         P (XK K) (bK K) sigma2 (PiK K))
    (hDescLocal : ∀ K : Real, 0 < K →
       Kyprianou.Ch06.IsAdmissibleLocalTimeAtMaximum
         P (FK K) (fun t omega => -XK K t omega) (Ldown K))
    (hE : ∀ q : Real, 0 < q →
       (∀ t : NNReal, P {omega | t < e q omega} =
         ENNReal.ofReal (Real.exp (-q * (t : Real)))) ∧
       (∀ (m : Nat) (times : Fin m → NNReal)
         (A : Fin m → Set Real) (B : Set NNReal),
         (∀ i, MeasurableSet (A i)) → MeasurableSet B →
         P {omega | e q omega ∈ B ∧
           (∀ i : Fin m, X (times i) omega ∈ A i)} =
         P {omega | e q omega ∈ B} *
         P {omega | ∀ i : Fin m, X (times i) omega ∈ A i})),
    ((∀ K : Real, 0 < K →
       (∀ t : NNReal, 0 < t →
         Integrable (fun omega => (XK K t omega) ^ n) P) ∧
       (∀ t : NNReal, 0 < t → ∀ k : Nat,
         Integrable (fun omega =>
           let tau := Kyprianou.Ch06.inverseLocalTime (Ldown K) t omega
           if tau = ⊤ then (0 : Real)
           else (Kyprianou.Ch06.runningMaximum
             (fun s w => -XK K s w) (tau.untopD 0) omega) ^ k) P)) ∧
     (∀ q : Real, 0 < q →
       Integrable (fun omega =>
         (Kyprianou.Ch06.runningMaximum X (e q omega) omega) ^ n) P) ∧
     ((∀ k : Nat, 2 ≤ k →
         (∫⁻ x : Real in Set.Ioi 1,
           ENNReal.ofReal (x ^ k) ∂Pi) < ⊤) →
       (∀ᵐ omega ∂P,
          ∃ M : Real, ∀ t : NNReal, X t omega ≤ M) →
       ∀ k : Nat, 2 ≤ k →
         Integrable (fun omega =>
           (sSup {y : Real | ∃ t : NNReal, y = X t omega}) ^ (k - 1)) P))

end Kyprianou.Ch07


