-- Prove2me | Definitions.Def_Kyprianou_Ch07_certificate_result_7_12
-- name    : Kyprianou_Ch07_certificate_result_7_12
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T14:57:48.40607+00:00
-- url     : https://prove2.me/theorems/fe94b88d-1a70-4362-90e4-b13e737177f7
-- title:
--   Full quantified certificate for pointHittingFourierCriterion
-- statement:
--   Source-exact closed quantified proposition obtained from the canonical parent theorem without dropping any binders or clauses.
-- source:
--   Kyprianou (2006), Theorem 7.12, printed p.199, source single-page PDF p.208, Windows Ky.pdf sheet 105.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Source-quantified full proposition of pointHittingFourierCriterion. -/
def certificate_result_7_12 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (b : Real) (sigma2 : NNReal) (Pi : Measure Real)
    (Psi : Real → Complex)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hNonCompound : ¬ Kyprianou.Ch06.IsCompoundPoissonProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ omega, Complex.exp
        (Complex.I * (↑(theta * X t omega) : Complex)) ∂P) =
      Complex.exp (-(↑(t : Real) : Complex) * Psi theta)),
    let C : Set Real := {x | 0 < P
       {omega : Omega | ∃ t : NNReal, 0 < t ∧ X t omega = x}}
    let hitsCriterion : Prop :=
      Integrable (fun theta : Real =>
        ((1 : Complex) / (1 + Psi theta)).re) volume
    let jumpFiniteVariation : Prop :=
      (∫⁻ x : Real in {x | |x| < 1},
        ENNReal.ofReal |x| ∂Pi) < ⊤
    let finiteVariation : Prop := sigma2 = 0 ∧ jumpFiniteVariation
    let effectiveDrift : Real :=
      b - ∫ x : Real in {x | |x| < 1}, x ∂Pi
    let upwardsSubordinator : Prop :=
      ∀ᵐ omega ∂P, Monotone (fun t : NNReal => X t omega)
    let downwardsSubordinator : Prop :=
      ∀ᵐ omega ∂P, Monotone (fun t : NNReal => -X t omega)
    ((C.Nonempty ↔ hitsCriterion) ∧
     (0 < sigma2 → hitsCriterion ∧ C = Set.univ) ∧
     (sigma2 = 0 → ¬ jumpFiniteVariation →
       hitsCriterion → C = Set.univ) ∧
     (finiteVariation →
       ((hitsCriterion ↔ effectiveDrift ≠ 0) ∧
        (effectiveDrift ≠ 0 →
          ((upwardsSubordinator → C = Set.Ioi 0) ∧
           (downwardsSubordinator → C = Set.Iio 0) ∧
           (¬ upwardsSubordinator → ¬ downwardsSubordinator →
             C = Set.univ))))))

end Kyprianou.Ch07


