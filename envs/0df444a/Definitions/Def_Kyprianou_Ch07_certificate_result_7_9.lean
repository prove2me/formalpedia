-- Prove2me | Definitions.Def_Kyprianou_Ch07_certificate_result_7_9
-- name    : Kyprianou_Ch07_certificate_result_7_9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T14:56:58.169073+00:00
-- url     : https://prove2.me/theorems/d7bcece0-cbd7-45d7-8302-6577751bae10
-- title:
--   Full quantified certificate for spectrallyPositiveAscendingLadderJumpTail
-- statement:
--   Source-exact closed quantified proposition obtained from the canonical parent theorem without dropping any binders or clauses.
-- source:
--   Kyprianou (2006), Corollary 7.9, printed p.196, original PDF physical p.205, Windows Ky.pdf sheet 103.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Source-quantified full proposition of spectrallyPositiveAscendingLadderJumpTail. -/
def certificate_result_7_9 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (F : NNReal → MeasurableSpace Omega)
    (Lup Ldown : NNReal → Omega → NNReal)
    (b : Real) (sigma2 : NNReal)
    (Pi PiH Uhat : Measure Real)
    (etaUp driftUp : Real) (phiUp : Real → Real)
    (Psi : Real → Complex)
    (psiDown : Real → Real) (phi0 : Real)
    (kappaUp kappaDown : Complex → Complex)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hNonCompound : ¬ Kyprianou.Ch06.IsCompoundPoissonProcess P X)
    (hXTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet
      P X b sigma2 Pi)
    (hSpectrallyPositive : Pi (Set.Iio 0) = 0)
    (hLocalUp : Kyprianou.Ch06.IsAdmissibleLocalTimeAtMaximum
      P F X Lup)
    (hLocalDown : Kyprianou.Ch06.IsAdmissibleLocalTimeAtMaximum
      P F (fun t omega => -X t omega) Ldown)
    (hHTriplet : Kyprianou.Ch05.IsKilledLaplaceTriplet
      etaUp driftUp PiH phiUp)
    (hAscendingLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega,
        let tau := Kyprianou.Ch06.inverseLocalTime Lup t omega
        if tau = ⊤ then (0 : Real)
        else Real.exp (-theta *
          Kyprianou.Ch06.runningMaximum X (tau.untopD 0) omega) ∂P) =
      Real.exp (-(t : Real) * phiUp theta))
    (hAscendingExponent : ∀ theta : Real, 0 ≤ theta →
      kappaUp (theta : Complex) = (phiUp theta : Complex))
    (hDescendingLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega,
        let tau := Kyprianou.Ch06.inverseLocalTime Ldown t omega
        if tau = ⊤ then (0 : Real)
        else Real.exp (-theta *
          Kyprianou.Ch06.runningMaximum (fun s w => -X s w)
            (tau.untopD 0) omega) ∂P) =
      Real.exp (-(t : Real) *
        (kappaDown (theta : Complex)).re))
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ omega, Complex.exp
        (Complex.I * (↑(theta * X t omega) : Complex)) ∂P) =
      Complex.exp (-(↑(t : Real) : Complex) * Psi theta))
    (hUpCharacteristic : ∀ (t : NNReal) (theta : Real),
      (∫ omega,
        let tau := Kyprianou.Ch06.inverseLocalTime Lup t omega
        if tau = ⊤ then (0 : Complex)
        else Complex.exp
          (Complex.I * (theta : Complex) *
            (↑(Kyprianou.Ch06.runningMaximum X
              (tau.untopD 0) omega) : Complex)) ∂P) =
        Complex.exp (-((t : Real) : Complex) *
          kappaUp (-(Complex.I * (theta : Complex)))))
    (hDownCharacteristic : ∀ (t : NNReal) (theta : Real),
      (∫ omega,
        let tau := Kyprianou.Ch06.inverseLocalTime Ldown t omega
        if tau = ⊤ then (0 : Complex)
        else Complex.exp
          (-(Complex.I * (theta : Complex)) *
            (↑(Kyprianou.Ch06.runningMaximum
              (fun s w => -X s w) (tau.untopD 0) omega) : Complex)) ∂P) =
        Complex.exp (-((t : Real) : Complex) *
          kappaDown (Complex.I * (theta : Complex))))
    (hWienerHopfNormalization : ∀ theta : Real,
      kappaUp (-(Complex.I * (theta : Complex))) *
        kappaDown (Complex.I * (theta : Complex)) = Psi theta)
    (hLaplaceDown : ∀ theta : Real, 0 ≤ theta →
      (∫ omega, Real.exp (-theta * X 1 omega) ∂P) =
        Real.exp (psiDown theta))
    (hPhi : 0 ≤ phi0 ∧ psiDown phi0 = 0 ∧
      (∀ theta : Real, 0 ≤ theta → psiDown theta = 0 → theta ≤ phi0))
    (hDescendingPotential : ∀ B : Set Real, MeasurableSet B →
      Uhat B =
        ∫⁻ t : Real in Set.Ici 0,
          P {omega | let tau :=
              Kyprianou.Ch06.inverseLocalTime Ldown (Real.toNNReal t) omega
            tau ≠ ⊤ ∧
              Kyprianou.Ch06.runningMaximum
                (fun s w => -X s w) (tau.untopD 0) omega ∈ B}
          ∂volume),
    ∀ y : Real, 0 < y →
      PiH (Set.Ioi y) =
        ∫⁻ z : Real in Set.Ici 0,
          ENNReal.ofReal (Real.exp (-phi0 * z)) *
            Pi (Set.Ioi (y + z)) ∂volume

end Kyprianou.Ch07


