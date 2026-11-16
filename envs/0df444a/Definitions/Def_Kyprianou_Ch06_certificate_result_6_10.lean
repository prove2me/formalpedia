-- Prove2me | Definitions.Def_Kyprianou_Ch06_certificate_result_6_10
-- name    : Kyprianou_Ch06_certificate_result_6_10
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:20:36.055197+00:00
-- url     : https://prove2.me/theorems/a12f42f9-52c3-4e78-ab86-7891ae5d959c
-- title:
--   Full quantified certificate for result:6.10
-- statement:
--   Exact fully quantified source theorem/exercise as a Prop, generated from the authoritative live theorem telescope and target with no conclusion weakening.
-- source:
--   Kyprianou (2006), Theorem 6.10, printed pp. 149–150; physical PDF p. 80.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_BivariateSubordinator
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Closed, full quantified source proposition from ascendingLadderSubordinatorDichotomy. -/
def certificate_result_6_10 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : NNReal → MeasurableSpace Omega)
    (X : NNReal → Omega → Real)
    (L : NNReal → Omega → NNReal)
    (hX : IsRealLevyProcess P X)
    (hLocal : IsAdmissibleLocalTimeAtMaximum P F X L),
    let bounded : Set Omega :=
      {omega | BddAbove (Set.range (fun t : NNReal => X t omega))}
    let totalLocalTime : Omega → WithTop NNReal := fun omega =>
      sSup ((fun t : NNReal => (L t omega : WithTop NNReal)) '' Set.univ)
    let ladder : NNReal → Omega → NNReal × NNReal := fun t omega =>
      ((inverseLocalTime L t omega).untopD 0,
        (runningMaximum X
          ((inverseLocalTime L t omega).untopD 0) omega).toNNReal)
    (P bounded = 0 ∨ P bounded = 1) ∧
    (P bounded = 0 →
      (∀ᵐ omega ∂P, ∀ t : NNReal,
        inverseLocalTime L t omega ≠ ⊤) ∧
      IsBivariateSubordinator P ladder) ∧
    (P bounded = 1 →
      (P {omega | ∀ t : NNReal, X t omega = 0} = 1 ∧
        (∀ᵐ omega ∂P, totalLocalTime omega = ⊤) ∧
        IsBivariateSubordinator P ladder) ∨
      (∃ q : Real, 0 < q ∧
        (∀ t : NNReal,
          P {omega | (t : WithTop NNReal) < totalLocalTime omega} =
            ENNReal.ofReal (Real.exp (-q * (t : Real)))) ∧
        ∃ Q : Measure ((NNReal → NNReal × NNReal) × NNReal),
          IsProbabilityMeasure Q ∧
          IsBivariateSubordinator Q (fun t z => z.1 t) ∧
          (∀ t : NNReal,
            Q {z | t < z.2} =
              ENNReal.ofReal (Real.exp (-q * (t : Real)))) ∧
          (∀ (k : Nat) (times : Fin k → NNReal)
            (A : Fin k → Set (NNReal × NNReal)) (B : Set NNReal),
            (∀ i, MeasurableSet (A i)) → MeasurableSet B →
            Q {z | z.2 ∈ B ∧
              (∀ i : Fin k, z.1 (times i) ∈ A i)} =
              Q {z | z.2 ∈ B} *
              Q {z | ∀ i : Fin k, z.1 (times i) ∈ A i}) ∧
          (∀ (k : Nat) (times : Fin k → NNReal)
            (A : Fin k → Set (Option (NNReal × NNReal))),
            (∀ i, MeasurableSet (A i)) →
            P {omega | ∀ i : Fin k,
              (if (times i : WithTop NNReal) <
                    totalLocalTime omega then
                 some (ladder (times i) omega)
               else none) ∈ A i} =
            Q {z | ∀ i : Fin k,
              (if times i < z.2 then
                 some (z.1 (times i)) else none) ∈ A i})))

end Kyprianou.Ch06


