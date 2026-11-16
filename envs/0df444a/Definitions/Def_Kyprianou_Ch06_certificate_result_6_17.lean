-- Prove2me | Definitions.Def_Kyprianou_Ch06_certificate_result_6_17
-- name    : Kyprianou_Ch06_certificate_result_6_17
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:22:52.524135+00:00
-- url     : https://prove2.me/theorems/9a8d2084-3353-40a9-b7c8-cf5db3c36f97
-- title:
--   Full quantified certificate for result:6.17
-- statement:
--   Exact fully quantified source theorem/exercise as a Prop, generated from the authoritative live theorem telescope and target with no conclusion weakening.
-- source:
--   Kyprianou (2006), Lemma 6.17, printed p. 160; two-up PDF p. 85.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_VectorLevyProcess
import Definitions.Def_Kyprianou_Ch06_TimePositionCharFun
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Closed, full quantified source proposition from exponentialSampledVectorLevyIsInfinitelyDivisible. -/
def certificate_result_6_17 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (d : Nat) (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → (Fin d → Real))
    (e : Omega → NNReal) (p : Real)
    (psi : (Fin d → Real) → Complex)
    (hp : 0 < p)
    (hX : IsVectorLevyProcess d P X)
    (hExp : ∀ t : NNReal,
      P {omega | t < e omega} =
        ENNReal.ofReal (Real.exp (-p * (t : Real))))
    (hExpIndependent :
      ∀ (k : Nat) (times : Fin k → NNReal)
        (A : Fin k → Set (Fin d → Real)) (B : Set NNReal),
        (∀ i, MeasurableSet (A i)) → MeasurableSet B →
        P {omega | e omega ∈ B ∧
          (∀ i : Fin k, X (times i) omega ∈ A i)} =
          P {omega | e omega ∈ B} *
          P {omega | ∀ i : Fin k, X (times i) omega ∈ A i})
    (hPsi : ∀ (t : NNReal) (theta : Fin d → Real),
      (∫ omega,
        Complex.exp (Complex.I *
          (↑(∑ i : Fin d, theta i * X t omega i) : Complex)) ∂P) =
      Complex.exp (-(↑(t : Real) : Complex) * psi theta))
    (hJointMeas : Measurable
      (fun omega => (e omega, X (e omega) omega))),
    let mu : Measure (NNReal × (Fin d → Real)) :=
      Measure.map (fun omega => (e omega, X (e omega) omega)) P
    (∀ n : Nat, 0 < n →
      ∃ nu : Measure (NNReal × (Fin d → Real)),
        IsProbabilityMeasure nu ∧
        ∀ (vartheta : Real) (theta : Fin d → Real),
          TimePositionCharFun d mu vartheta theta =
            (TimePositionCharFun d nu vartheta theta) ^ n) ∧
    (∀ (vartheta : Real) (theta : Fin d → Real),
      TimePositionCharFun d mu vartheta theta =
        Complex.exp (-
          (∫ t in Set.Ioi (0 : Real),
            (Complex.exp (-(↑(p * t) : Complex)) /
               (↑t : Complex)) *
            (1 - ∫ omega,
              Complex.exp (Complex.I *
                (↑(vartheta * t +
                  ∑ i : Fin d, theta i *
                    X t.toNNReal omega i) : Complex)) ∂P) ∂volume)) ∧
      TimePositionCharFun d mu vartheta theta =
        (↑p : Complex) /
          ((↑p : Complex) -
            Complex.I * (↑vartheta : Complex) + psi theta))

end Kyprianou.Ch06


