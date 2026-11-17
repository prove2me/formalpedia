-- Prove2me | Definitions.Def_Kyprianou_Ch07_certificate_exercise_7_6
-- name    : Kyprianou_Ch07_certificate_exercise_7_6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T14:59:02.771761+00:00
-- url     : https://prove2.me/theorems/30017d26-8571-4745-9f5e-078622271259
-- title:
--   Full quantified certificate for exercise7_6CreepingHittingAllParts
-- statement:
--   Source-exact closed quantified proposition obtained from the canonical parent theorem without dropping any binders or clauses.
-- source:
--   Kyprianou (2006), Exercise 7.6(i)–(v), printed pp.208–209; original PDF physical pp.217–218; Windows Ky.pdf sheets 109–110.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Source-quantified full proposition of exercise7_6CreepingHittingAllParts. -/
def certificate_exercise_7_6 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (b : Real) (sigma2 : NNReal) (Pi : Measure Real)
    (Psi : Real → Complex)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ omega, Complex.exp
        (Complex.I * (↑(theta * X t omega) : Complex)) ∂P) =
      Complex.exp (-(↑(t : Real) : Complex) * Psi theta)),
    let upCreeps : Prop :=
      0 < Kyprianou.Ch05.creepingProbability
        P X (fun _ => (⊤ : WithTop NNReal)) 1
    let downCreeps : Prop :=
      0 < Kyprianou.Ch05.creepingProbability
        P (fun t omega => -X t omega)
          (fun _ => (⊤ : WithTop NNReal)) 1
    let finiteVariationJumpMass : Prop :=
      (∫⁻ x : Real in {x | |x| < 1},
        ENNReal.ofReal |x| ∂Pi) < ⊤
    let canonicalDrift : Real :=
      b - ∫ x : Real in {x | |x| < 1}, x ∂Pi
    ((Tendsto (fun theta : Real =>
         Psi theta / ((theta ^ 2 : Real) : Complex))
         (Filter.comap (fun theta : Real => |theta|) atTop)
         (nhds (((sigma2 : Real) / 2 : Real) : Complex)) ∧
       ((upCreeps ∧ downCreeps) ↔ 0 < sigma2)) ∧
     ((sigma2 = 0 ∧ finiteVariationJumpMass) →
       (upCreeps ↔ 0 < canonicalDrift)) ∧
     (Kyprianou.Ch06.IsIrregularFor P X 0 (Set.Ioi 0) →
       ¬ upCreeps) ∧
     (sigma2 = 0 → Pi (Set.Ioi 0) = 0 →
       (¬ ∀ᵐ omega ∂P,
         Monotone (fun t : NNReal => -X t omega)) →
       ¬ downCreeps) ∧
     (∀ alpha : Real, 1 < alpha → alpha < 2 →
       (∃ c : Real, 0 < c ∧ ∀ theta : Real,
         Psi theta = ((c * |theta| ^ alpha : Real) : Complex)) →
       (¬ upCreeps ∧ ¬ downCreeps ∧
         ∀ x : Real, 0 < P {omega : Omega |
           ∃ t : NNReal, 0 < t ∧ X t omega = x})))

end Kyprianou.Ch07


