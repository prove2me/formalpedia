-- Prove2me | Definitions.Def_Kyprianou_Ch07_certificate_result_7_6
-- name    : Kyprianou_Ch07_certificate_result_7_6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T14:59:55.161942+00:00
-- url     : https://prove2.me/theorems/768e8d46-c417-4f12-a59d-140c84465f66
-- title:
--   Full quantified certificate for cramerExponentialRuinAsymptotic
-- statement:
--   Source-exact closed quantified proposition obtained from the canonical parent theorem without dropping any binders or clauses.
-- source:
--   Kyprianou (2006), Theorem 7.6(i)–(iii) and equation (7.6), printed pp.185–186, original PDF physical pp.194–195, Windows Ky.pdf sheets 98.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Source-quantified full proposition of cramerExponentialRuinAsymptotic. -/
def certificate_result_7_6 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (F : NNReal → MeasurableSpace Omega)
    (Lup : NNReal → Omega → NNReal)
    (b : Real) (sigma2 : NNReal) (Pi : Measure Real)
    (psi kappa : Real → Real)
    (nu : Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet
      P X b sigma2 Pi)
    (hNoMonotonePaths :
      (¬ ∀ᵐ omega ∂P, Monotone (fun t : NNReal => X t omega)) ∧
      (¬ ∀ᵐ omega ∂P, Monotone (fun t : NNReal => -X t omega)))
    (hDriftsDown : ∀ᵐ omega ∂P,
      Tendsto (fun t : NNReal => X t omega) atTop atBot)
    (hNu : 0 < nu)
    (hMGF : ∀ theta : Real, 0 ≤ theta → theta ≤ nu →
      (∫ omega, Real.exp (theta * X 1 omega) ∂P) =
        Real.exp (psi theta))
    (hCramer : psi nu = 0)
    (hNonLattice : Pi Set.univ < ⊤ →
      ∀ delta : Real, 0 < delta →
        0 < Pi {x : Real | ∀ k : Int, x ≠ delta * (k : Real)})
    (hLocalTime : Kyprianou.Ch06.IsAdmissibleLocalTimeAtMaximum
      P F X Lup)
    (hAscLaplace : ∀ theta : Real, -nu ≤ theta →
      ∀ t : NNReal,
      (∫ omega,
        let tau := Kyprianou.Ch06.inverseLocalTime Lup t omega
        if tau = ⊤ then (0 : Real)
        else Real.exp (-theta *
          Kyprianou.Ch06.runningMaximum X (tau.untopD 0) omega) ∂P) =
        Real.exp (-(t : Real) * kappa theta)),
    ∃ derivativeAtMinusNu : ENNReal,
      0 < kappa 0 ∧
      0 < derivativeAtMinusNu ∧
      Tendsto
        (fun h : Real => ENNReal.ofReal
          ((kappa (-nu + h) - kappa (-nu)) / h))
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds derivativeAtMinusNu) ∧
      Tendsto (fun x : Real =>
        Real.exp (nu * x) *
          (P {omega | Kyprianou.Ch05.PassageFinite
            X (fun _ => (⊤ : WithTop NNReal)) x omega}).toReal)
        atTop
        (nhds ((ENNReal.ofReal (kappa 0) /
          (ENNReal.ofReal nu * derivativeAtMinusNu)).toReal))

end Kyprianou.Ch07


