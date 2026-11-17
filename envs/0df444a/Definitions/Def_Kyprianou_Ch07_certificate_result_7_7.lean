-- Prove2me | Definitions.Def_Kyprianou_Ch07_certificate_result_7_7
-- name    : Kyprianou_Ch07_certificate_result_7_7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T15:04:16.529177+00:00
-- url     : https://prove2.me/theorems/0a3abd9c-97df-4f82-a81b-7314d9e89889
-- title:
--   Full quantified certificate for quintupleFirstPassageLaw
-- statement:
--   Source-exact closed quantified proposition obtained from the canonical parent theorem without dropping any binders or clauses.
-- source:
--   Kyprianou (2006), Theorem 7.7, printed p.191, original PDF page 200, Windows Ky.pdf sheet 101.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
import Definitions.Def_Kyprianou_Ch07_QuintuplePrePassageObservables
open MeasureTheory Filter Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Source-quantified full proposition of quintupleFirstPassageLaw. -/
def certificate_result_7_7 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X Xleft : NNReal → Omega → Real)
    (F : NNReal → MeasurableSpace Omega)
    (Lup Ldown : NNReal → Omega → NNReal)
    (b : Real) (sigma2 : NNReal)
    (Pi : Measure Real)
    (U Uhat : Measure (NNReal × Real))
    (Psi : Real → Complex)
    (kappaUp kappaDown : Complex → Complex)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hNonCompound : ¬ Kyprianou.Ch06.IsCompoundPoissonProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi)
    (hLeft : Kyprianou.Ch05.IsLeftLimitVersion P X Xleft)
    (hUp : Kyprianou.Ch06.IsAdmissibleLocalTimeAtMaximum P F X Lup)
    (hDown : Kyprianou.Ch06.IsAdmissibleLocalTimeAtMaximum
       P F (fun t omega => -X t omega) Ldown)
    (hUPotential : ∀ C : Set (NNReal × Real), MeasurableSet C →
       U C = ∫⁻ s : Real in Set.Ici 0,
         P {omega | let tau :=
           Kyprianou.Ch06.inverseLocalTime Lup (Real.toNNReal s) omega
           tau ≠ ⊤ ∧
           ((tau.untopD 0),
            Kyprianou.Ch06.runningMaximum X (tau.untopD 0) omega) ∈ C}
          ∂volume)
    (hUhatPotential : ∀ C : Set (NNReal × Real), MeasurableSet C →
       Uhat C = ∫⁻ s : Real in Set.Ici 0,
         P {omega | let tau :=
           Kyprianou.Ch06.inverseLocalTime Ldown (Real.toNNReal s) omega
           tau ≠ ⊤ ∧
           ((tau.untopD 0),
            Kyprianou.Ch06.runningMaximum
              (fun t omega => -X t omega) (tau.untopD 0) omega) ∈ C}
          ∂volume)
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
    (hWienerHopfNormalisation : ∀ theta : Real,
      kappaUp (-(Complex.I * (theta : Complex))) *
        kappaDown (Complex.I * (theta : Complex)) = Psi theta),
    ∀ x : Real, 0 < x →
      ∀ (At As : Set NNReal) (Au Av Ay : Set Real),
      MeasurableSet At → MeasurableSet As →
      MeasurableSet Au → MeasurableSet Av → MeasurableSet Ay →
      (∀ u : Real, u ∈ Au → 0 < u) →
      (∀ v : Real, v ∈ Av → 0 ≤ v) →
      (∀ y : Real, y ∈ Ay → 0 ≤ y ∧ y ≤ x) →
      P {omega | let lifetime : Omega → WithTop NNReal := fun _ => ⊤
        let tau := Kyprianou.Ch05.passageFiniteTime X lifetime x omega
        let g := lastMaximumContactBeforeUpcrossing X x omega
        let high := maximumBeforeUpcrossing X x omega
        Kyprianou.Ch05.PassageFinite X lifetime x omega ∧
        (tau - g) ∈ At ∧ g ∈ As ∧
        (X tau omega - x) ∈ Au ∧
        (x - Xleft tau omega) ∈ Av ∧
        (x - high) ∈ Ay} =
      ∫⁻ sh : NNReal × Real in
        {sh | sh.1 ∈ As ∧ 0 ≤ sh.2 ∧ sh.2 ≤ x},
        (∫⁻ tz : NNReal × Real in
          {tz | tz.1 ∈ At ∧ 0 ≤ tz.2},
          (if (x - sh.2) ∈ Ay ∧
              (x - sh.2 + tz.2) ∈ Av
           then Pi {z : Real |
             0 < z - (x - sh.2 + tz.2) ∧
             z - (x - sh.2 + tz.2) ∈ Au}
           else 0) ∂Uhat) ∂U

end Kyprianou.Ch07


