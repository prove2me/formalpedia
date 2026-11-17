-- Prove2me | Definitions.Def_Kyprianou_Ch07_certificate_exercise_7_3
-- name    : Kyprianou_Ch07_certificate_exercise_7_3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T15:05:01.3648+00:00
-- url     : https://prove2.me/theorems/19cd13d0-fb8b-4b96-805a-ecd9ebb38b59
-- title:
--   Full quantified certificate for exercise7_3SpectrallyNegativeWienerHopfAllParts
-- statement:
--   Full quantified source proposition of Kyprianou.Ch07.exercise7_3SpectrallyNegativeWienerHopfAllParts with source-fidelity repairs; every binder and clause is retained.
-- source:
--   Kyprianou (2006), Exercise 7.3(i)–(iv), printed p.207, original PDF p.216, Windows Ky.pdf sheet 109.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch07_DriftOscillationObservables
open MeasureTheory Filter Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Source-quantified full proposition of exercise7_3SpectrallyNegativeWienerHopfAllParts. -/
def certificate_exercise_7_3 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (b : Real) (sigma2 : NNReal) (Pi : Measure Real)
    (psi : Real → Real) (Phi0 : Real) (drift : WithBot Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi)
    (hSpectralNegative : Pi (Set.Ioi 0) = 0)
    (hNotNegativeSubordinator :
      ¬ ∀ᵐ omega ∂P, Monotone (fun t : NNReal => -X t omega))
    (hLaplace : ∀ theta : Real, 0 ≤ theta →
       (∫ omega, Real.exp (theta * X 1 omega) ∂P) =
         Real.exp (psi theta))
    (hPsi0 : psi 0 = 0)
    (hDerivative : Tendsto
      (fun theta : Real =>
        (((psi theta - psi 0) / theta : Real) : WithBot Real))
      (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds drift))
    (hPhi : 0 ≤ Phi0 ∧ psi Phi0 = 0 ∧
       ∀ theta : Real, 0 ≤ theta → psi theta = 0 → theta ≤ Phi0),
    let infFinite : Omega → Prop := fun omega =>
      ∃ M : Real, ∀ t : NNReal, -M ≤ X t omega
    let supFinite : Omega → Prop := fun omega =>
      ∃ M : Real, ∀ t : NNReal, X t omega ≤ M
    let infimum : Omega → Real := fun omega =>
      sInf {x : Real | ∃ t : NNReal, x = X t omega}
    let supremum : Omega → Real := fun omega =>
      sSup {x : Real | ∃ t : NNReal, x = X t omega}
    ((∀ beta : Real, 0 < beta →
       ((drift < 0 →
          (∫ omega, if infFinite omega
            then Real.exp (beta * infimum omega) else 0 ∂P) = 0) ∧
        (∀ d : Real, drift = (d : WithBot Real) → 0 ≤ d →
          (∫ omega, if infFinite omega
            then Real.exp (beta * infimum omega) else 0 ∂P) =
               d * beta / psi beta))) ∧
     (∀ beta : Real, 0 < beta →
       ((drift < 0 →
         (∫ omega, if supFinite omega
           then Real.exp (-beta * supremum omega) else 0 ∂P) =
           Phi0 / (beta + Phi0)) ∧
        ((0 : WithBot Real) ≤ drift →
         (∫ omega, if supFinite omega
           then Real.exp (-beta * supremum omega) else 0 ∂P) = 0))) ∧
     ((0 : WithBot Real) < drift → DriftsToPosInfinity P X) ∧
     (drift < 0 → DriftsToNegInfinity P X) ∧
     (drift = (0 : WithBot Real) → OscillatesAtInfinity P X) ∧
     (∀ alpha c : Real, 1 < alpha → alpha < 2 → 0 < c →
       (∀ theta : Real, 0 ≤ theta → psi theta = c * theta ^ alpha) →
       OscillatesAtInfinity P X))

end Kyprianou.Ch07


