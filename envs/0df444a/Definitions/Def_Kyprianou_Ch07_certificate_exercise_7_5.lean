-- Prove2me | Definitions.Def_Kyprianou_Ch07_certificate_exercise_7_5
-- name    : Kyprianou_Ch07_certificate_exercise_7_5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T15:06:01.69955+00:00
-- url     : https://prove2.me/theorems/20e0c90c-b9cd-482f-b9c3-f6e91bbe4b18
-- title:
--   Full quantified certificate for exercise7_5BivariateAscendingLadderJumpMeasure
-- statement:
--   Full quantified source proposition of Kyprianou.Ch07.exercise7_5BivariateAscendingLadderJumpMeasure with source-fidelity repairs; every binder and clause is retained. Includes explicit Chapter 7 standing exclusion of subordinators.
-- source:
--   Kyprianou (2006), Exercise 7.5, both formulae printed p.208; original PDF page 217, Windows Ky.pdf sheet 109.

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

/-- Source-quantified full proposition of exercise7_5BivariateAscendingLadderJumpMeasure. -/
def certificate_exercise_7_5 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (F : NNReal → MeasurableSpace Omega)
    (Lup Ldown : NNReal → Omega → NNReal)
    (b : Real) (sigma2 : NNReal)
    (Pi : Measure Real)
    (PiAsc Uhat : Measure (NNReal × Real))
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hNonCompound : ¬ Kyprianou.Ch06.IsCompoundPoissonProcess P X)
    (hNotSubordinator : ¬ Kyprianou.Ch06.IsSubordinatorProcess P X)
    (hXTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi)
    (hUp : Kyprianou.Ch06.IsAdmissibleLocalTimeAtMaximum P F X Lup)
    (hDown : Kyprianou.Ch06.IsAdmissibleLocalTimeAtMaximum
      P F (fun t omega => -X t omega) Ldown)
    (hWienerHopfScale :
      Real.log
        (∫ omega,
          let tau := Kyprianou.Ch06.inverseLocalTime Lup 1 omega
          if tau = ⊤ then (0 : Real)
          else Real.exp (-((tau.untopD (0 : NNReal) : NNReal) : Real)) ∂P) *
      Real.log
        (∫ omega,
          let tau := Kyprianou.Ch06.inverseLocalTime Ldown 1 omega
          if tau = ⊤ then (0 : Real)
          else Real.exp (-((tau.untopD (0 : NNReal) : NNReal) : Real)) ∂P) = 1)
    (hSpectralPositiveUnitDescendingHeight :
      Pi (Set.Iio 0) = 0 →
      ∀ᵐ omega ∂P, ∀ s : NNReal,
        let tau := Kyprianou.Ch06.inverseLocalTime Ldown s omega
        tau ≠ ⊤ → 0 < tau.untopD 0 →
          Kyprianou.Ch06.runningMaximum
            (fun t w => -X t w) (tau.untopD 0) omega = (s : Real))
    (hAscJumpMeasure : ∀ B : Set (NNReal × Real),
      MeasurableSet B → (0 : NNReal × Real) ∉ B →
      Tendsto (fun h : Real =>
        ENNReal.ofReal (1 / h) *
          (∫⁻ omega,
            (∑' s : NNReal,
              if 0 < s ∧ s ≤ Real.toNNReal h then
                let tau := Kyprianou.Ch06.inverseLocalTime Lup s omega
                let tauLeft :=
                  Kyprianou.Ch06.inverseLocalTimeLeft Lup s omega
                if tau ≠ ⊤ ∧ tauLeft ≠ ⊤ ∧
                    ((tau.untopD 0 - tauLeft.untopD 0),
                     Kyprianou.Ch06.runningMaximum X (tau.untopD 0) omega -
                     Kyprianou.Ch06.runningMaximum X (tauLeft.untopD 0) omega)
                      ∈ B
                then (1 : ENNReal) else 0
              else 0) ∂P))
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (PiAsc B)))
    (hUhat : ∀ B : Set (NNReal × Real), MeasurableSet B →
      Uhat B =
        ∫⁻ s : Real in Set.Ici 0,
          P {omega | let tau :=
            Kyprianou.Ch06.inverseLocalTime Ldown (Real.toNNReal s) omega
            tau ≠ ⊤ ∧
            ((tau.untopD 0),
             Kyprianou.Ch06.runningMaximum
                (fun t omega => -X t omega) (tau.untopD 0) omega) ∈ B}
          ∂volume),
    ((∀ (At : Set NNReal) (Ah : Set Real),
      MeasurableSet At → MeasurableSet Ah →
      (∀ h : Real, h ∈ Ah → 0 < h) →
      PiAsc {zh | zh.1 ∈ At ∧ zh.2 ∈ Ah} =
        ∫⁻ zt : NNReal × Real in {zt | zt.1 ∈ At ∧ 0 ≤ zt.2},
          Pi {z : Real | z - zt.2 ∈ Ah} ∂Uhat) ∧
     (Pi (Set.Iio 0) = 0 →
       ∀ (At : Set NNReal) (Ah : Set Real),
       MeasurableSet At → MeasurableSet Ah →
       (∀ h : Real, h ∈ Ah → 0 < h) →
       PiAsc {zh | zh.1 ∈ At ∧ zh.2 ∈ Ah} =
         ∫⁻ theta : Real in Set.Ici 0,
           P {omega | let tau :=
             (Kyprianou.Ch06.inverseLocalTime Ldown
               (Real.toNNReal theta) omega)
             tau ≠ ⊤ ∧ (tau.untopD 0) ∈ At} *
           Pi {z : Real | z - theta ∈ Ah} ∂volume))

end Kyprianou.Ch07


