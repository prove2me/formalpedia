-- Prove2me | Definitions.Def_Kyprianou_Ch04_Exercise4_1CertificationV2
-- name    : Kyprianou_Ch04_Exercise4_1CertificationV2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T10:16:01.010285+00:00
-- url     : https://prove2.me/theorems/c5f5ae84-be81-4956-a9ab-1fd70891a9fd
-- title:
--   Exercise 4.1 corrected complete-source certificate (review v2)
-- statement:
--   The complete Exercise 4.1 includes finite zero-visit counting and a change-of-variable identity for functions separately C1 on either side of zero with arbitrary f(0). The boundary correction counts the initial right departure, continuous arrivals from below, and the right departure after every completed zero visit. Jumps landing at zero are already accounted for by the raw jump integral.
-- source:
--   Kyprianou (2006), Chapter 4 Exercise 4.1, pp.105-109.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04

noncomputable def certificate_ex4_1_i_v2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift),
    ∀ᵐ omega : Omega ∂P,
          (∀ t : NNReal,
            Set.Finite {s : NNReal | 0 < s ∧ s ≤ t ∧ L.X s omega = 0}) ∧
          (∀ t : NNReal,
            ContinuousWithinAt
              (fun u : NNReal =>
                (({s : NNReal | 0 < s ∧ s ≤ u ∧ L.X s omega = 0}).ncard : Real))
              (Set.Ici t) t) ∧
          (∀ t : NNReal, 0 < t →
            ∃ l : Real,
              Tendsto
                (fun u : NNReal =>
                  (({s : NNReal | 0 < s ∧ s ≤ u ∧ L.X s omega = 0}).ncard : Real))
                (nhdsWithin t (Set.Iio t)) (nhds l))

noncomputable def certificate_ex4_1_ii_v2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (Xleft : NNReal -> Omega -> Real)
    (hLeft : ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s : NNReal => L.X s omega)
        (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
    (f fLeft fRight : Real -> Real)
    (hC1Left : ContDiff Real 1 fLeft)
    (hC1Right : ContDiff Real 1 fRight)
    (hPieceLeft : ∀ x : Real, x < 0 -> f x = fLeft x)
    (hPieceRight : ∀ x : Real, 0 < x -> f x = fRight x),
    ∀ᵐ omega : Omega ∂P,
          ∀ (hVisits : ∀ t : NNReal,
            Set.Finite {s : NNReal | 0 < s ∧ s ≤ t ∧ L.X s omega = 0})
            (t : NNReal),
            f (L.X t omega) =
              f (L.X 0 omega) +
              L.drift *
                (∫ s in Set.Icc (0 : Real) (t : Real),
                  (if L.X (Real.toNNReal s) omega < 0 then
                    deriv fLeft (L.X (Real.toNNReal s) omega)
                   else if 0 < L.X (Real.toNNReal s) omega then
                    deriv fRight (L.X (Real.toNNReal s) omega)
                   else 0) ∂volume) +
              (∫ z in Set.prod (Set.Ioc (0 : Real) (t : Real)) (Set.Iio 0),
                (f (Xleft (Real.toNNReal z.1) omega + z.2) -
                  f (Xleft (Real.toNNReal z.1) omega))
                  ∂(Kyprianou.Ch04.pathJumpMeasure L.X Xleft omega)) +
              (if 0 < t then fRight 0 - f 0 else 0) +
              Finset.sum (hVisits t).toFinset
                (fun s : NNReal =>
                  (if Xleft s omega = 0 then f 0 - fLeft 0 else 0) +
                  (if s < t then fRight 0 - f 0 else 0))

/-- All textbook subparts of Exercise 4.1 are required, with none silently omitted. -/
noncomputable def certificate_exercise_4_1_v2 : Prop :=
    certificate_ex4_1_i_v2 ∧
    certificate_ex4_1_ii_v2

end Kyprianou.Ch04


