-- Prove2me | Definitions.Def_Kyprianou_Ch06_certificate_result_6_15
-- name    : Kyprianou_Ch06_certificate_result_6_15
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:21:51.119202+00:00
-- url     : https://prove2.me/theorems/8cc92c62-670c-46f3-be12-0791b99563c8
-- title:
--   Full quantified certificate for result:6.15
-- statement:
--   Exact fully quantified source theorem/exercise as a Prop, generated from the authoritative live theorem telescope and target with no conclusion weakening.
-- source:
--   Kyprianou (2006), Theorem 6.15, printed pp. 155–156; physical PDF p. 83.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
import Definitions.Def_Kyprianou_Ch06_ExcursionSpace
import Definitions.Def_Kyprianou_Ch06_ExcursionCountAtLocalTime
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Closed, full quantified source proposition from excursionPointProcessWithPossibleKilling. -/
def certificate_result_6_15 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (F : NNReal → MeasurableSpace Omega)
    (L : NNReal → Omega → NNReal)
    (hX : IsRealLevyProcess P X)
    (hLocal : IsAdmissibleLocalTimeAtMaximum P F X L),
    ∃ (Sigma : MeasurableSpace
        ((NNReal → Real) × WithTop NNReal)),
      letI : MeasurableSpace
        ((NNReal → Real) × WithTop NNReal) := Sigma
      ∃ (n : Measure ((NNReal → Real) × WithTop NNReal))
        (cover : Nat → Set ((NNReal → Real) × WithTop NNReal)),
      (∀ k, MeasurableSet (cover k) ∧ n (cover k) < ⊤) ∧
      (⋃ k, cover k) = Set.univ ∧
      MeasurableSet ExcursionSpace ∧
      n ExcursionSpaceᶜ = 0 ∧
      Measurable (fun e : (NNReal → Real) × WithTop NNReal => e.2) ∧
      Measurable (fun e : (NNReal → Real) × WithTop NNReal =>
        e.1 (e.2.untopD 0)) ∧
      Measurable (fun e : (NNReal → Real) × WithTop NNReal =>
        -sInf (e.1 '' {t : NNReal |
          0 < t ∧ (t : WithTop NNReal) < e.2})) ∧
      (P {omega |
        ¬ BddAbove (Set.range (fun t : NNReal => X t omega))} = 1 →
        IsMarkedPoissonPointProcess P n
          (fun omega t A =>
            excursionCountAtLocalTime X L omega t A)) ∧
      (P {omega |
        BddAbove (Set.range (fun t : NNReal => X t omega))} = 1 →
        ∃ Q : Measure
          (NNReal → Option ((NNReal → Real) × WithTop NNReal)),
          IsProbabilityMeasure Q ∧
          IsMarkedPoissonPointProcess Q n
            (fun z t A =>
              ({s : NNReal | 0 < s ∧ s ≤ t ∧
                ∃ e, z s = some e ∧ e ∈ A}).ncard) ∧
          (∀ (k : Nat) (times : Fin k → NNReal)
            (A : Fin k → Set ((NNReal → Real) × WithTop NNReal))
            (counts : Fin k → Nat),
            (∀ i, MeasurableSet (A i) ∧ n (A i) < ⊤) →
            P {omega | ∀ i : Fin k,
              ({s : NNReal |
                0 < s ∧ s ≤ times i ∧
                (s : WithTop NNReal) <
                  sSup ((fun u : NNReal =>
                    (L u omega : WithTop NNReal)) '' Set.univ) ∧
                ∃ e, indexedExcursion X L s omega =
                  some e ∧ e ∈ A i}).ncard = counts i} =
            Q {z | ∀ i : Fin k,
              ({s : NNReal | 0 < s ∧ s ≤ times i ∧
                (s : WithTop NNReal) <
                  sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
                    {u : NNReal | 0 < u ∧
                      ∃ e, z u = some e ∧ e.2 = ⊤}) ∧
                ∃ e, z s = some e ∧ e ∈ A i}).ncard =
                counts i}))

end Kyprianou.Ch06


