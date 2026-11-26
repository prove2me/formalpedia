-- Prove2me | Definitions.Def_Kyprianou_Ch04_Exercise4_4CertificationV3
-- name    : Kyprianou_Ch04_Exercise4_4CertificationV3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-26T07:49:17.174445+00:00
-- url     : https://prove2.me/theorems/c4586cfd-85c0-40ea-b2d4-bb08413afcfa
-- title:
--   Corrected Exercise 4.4 complete certification
-- statement:
--   Corrected complete Exercise 4.4 certificate retaining the entire second-moment identity, with exact past count adaptedness and common-null markwise left continuity.
-- source:
--   Kyprianou (2006), Exercise 4.4

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory ProbabilityTheory Filter ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04

noncomputable def certificate_ex4_4_main_v3 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (hPast : forall (u : NNReal) (B : Set (Real × Real)),
      MeasurableSet B →
      B ⊆ Set.prod (Set.Icc (0 : Real) (u : Real)) Set.univ →
      Measurable[F u] (fun omega => N.N omega B))
    (phi : Real -> Real -> Omega -> Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (hCommon : ∀ᵐ omega ∂P, ∀ (x : Real) (t : NNReal), 0 < t →
      Tendsto (fun s : Real => phi s x omega)
        (nhdsWithin (t : Real) (Set.Iio (t : Real)))
        (nhds (phi (t : Real) x omega)))
    (hL1 : forall t : NNReal,
      (∫⁻ omega,
        (∫⁻ s in Set.Icc (0 : Real) (t : Real),
          (∫⁻ x, ENNReal.ofReal (phi s x omega) ∂levyMeasure)
          ∂volume) ∂P) < ⊤)
    (hL2 : forall t : NNReal,
      (∫⁻ omega,
        (∫⁻ s in Set.Icc (0 : Real) (t : Real),
          (∫⁻ x, ENNReal.ofReal ((phi s x omega) ^ 2) ∂levyMeasure)
          ∂volume) ∂P) < ⊤),
    forall t : NNReal,
          (∫ omega,
            ((∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
                phi z.1 z.2 omega ∂(N.N omega)) -
              (∫ s in Set.Icc (0 : Real) (t : Real),
                (∫ x, phi s x omega ∂levyMeasure) ∂volume)) ^ 2 ∂P) =
          (∫ omega,
            (∫ s in Set.Icc (0 : Real) (t : Real),
              (∫ x, (phi s x omega) ^ 2 ∂levyMeasure)
              ∂volume) ∂P)

/-- All textbook subparts of Exercise 4.4 are required, with none silently omitted. -/
noncomputable def certificate_exercise_4_4_v3 : Prop :=
    certificate_ex4_4_main_v3

end Kyprianou.Ch04


