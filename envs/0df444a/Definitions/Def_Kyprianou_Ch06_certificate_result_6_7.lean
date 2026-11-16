-- Prove2me | Definitions.Def_Kyprianou_Ch06_certificate_result_6_7
-- name    : Kyprianou_Ch06_certificate_result_6_7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:19:21.033141+00:00
-- url     : https://prove2.me/theorems/f515c7e5-d05d-40e0-b2ef-b6ccb3bad53a
-- title:
--   Full quantified certificate for result:6.7
-- statement:
--   Exact fully quantified source theorem/exercise as a Prop, generated from the authoritative live theorem telescope and target with no conclusion weakening.
-- source:
--   Kyprianou (2006), Theorem 6.7(i)–(ii), printed pp. 144–145; two-up PDF pp. 77–78.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Closed, full quantified source proposition from continuousOrMarkedLocalTimeAtMaximum. -/
def certificate_result_6_7 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : NNReal → MeasurableSpace Omega)
    (X : NNReal → Omega → Real)
    (hX : IsRealLevyProcess P X)
    (hF : IsFiltration F ∧ IsRightContinuousFiltration F)
    (hAdapted : ∀ t : NNReal,
      @Measurable Omega Real (F t) inferInstance (X t))
    (hIndependentOfPast : ∀ (s : NNReal) (k : Nat)
      (times : Fin k → NNReal) (A : Fin k → Set Real)
      (B : Set Omega),
      (∀ i, MeasurableSet (A i)) →
      @MeasurableSet Omega (F s) B →
      P {omega | omega ∈ B ∧
        (∀ i : Fin k,
          X (s + times i) omega - X s omega ∈ A i)} =
      P B *
        P {omega | ∀ i : Fin k, X (times i) omega ∈ A i}),
    ((∃ L : NNReal → Omega → NNReal,
      IsContinuousLocalTimeAtMaximum P F X L ∧
      ∀ L' : NNReal → Omega → NNReal,
        IsContinuousLocalTimeAtMaximum P F X L' →
        ∃ c : Real, 0 < c ∧
          ∀ᵐ omega ∂P, ∀ t : NNReal,
            (L' t omega : Real) = c * (L t omega : Real)) ↔
      IsRegularFor P X 0 (Set.Ici 0)) ∧
    ((IsIrregularFor P X 0 (Set.Ici 0)) →
      ∀ lambda : Real, 0 < lambda →
        ∃ (Q : Measure (Omega × (Nat → NNReal)))
          (Fext : NNReal →
            MeasurableSpace (Omega × (Nat → NNReal)))
          (n : NNReal → Omega → Nat)
          (L : NNReal → (Omega × (Nat → NNReal)) → NNReal),
          IsProbabilityMeasure Q ∧
          Measure.map Prod.fst Q = P ∧
          (∀ t : NNReal, ∀ᵐ z ∂Q,
            L t z = ∑ i ∈ Finset.range (n t z.1 + 1), z.2 i) ∧
          (∀ᵐ omega ∂P, ∀ t : NNReal,
            Set.Finite {s : NNReal |
              0 < s ∧ s ≤ t ∧
                X s omega = runningMaximum X s omega}) ∧
          (∀ᵐ omega ∂P, ∀ t : NNReal,
            n t omega =
              ({s : NNReal |
                0 < s ∧ s ≤ t ∧
                  X s omega = runningMaximum X s omega}).ncard) ∧
          (∀ (i : Nat) (t : NNReal),
            Q {z | t < z.2 i} =
              ENNReal.ofReal (Real.exp (-lambda * (t : Real)))) ∧
          (∀ (k : Nat) (A : Fin k → Set NNReal),
            (∀ i, MeasurableSet (A i)) →
            Q {z | ∀ i : Fin k, z.2 i ∈ A i} =
              ∏ i : Fin k, Q {z | z.2 i ∈ A i}) ∧
          (∀ (k : Nat) (A : Fin k → Set NNReal)
            (B : Set Omega),
            (∀ i, MeasurableSet (A i)) → MeasurableSet B →
            Q {z | z.1 ∈ B ∧
              (∀ i : Fin k, z.2 i ∈ A i)} =
              P B * Q {z | ∀ i : Fin k, z.2 i ∈ A i}) ∧
          IsAdmissibleLocalTimeAtMaximum Q Fext
            (fun t z => X t z.1) L)

end Kyprianou.Ch06


