-- Prove2me | Definitions.Def_Kyprianou_Ch04_Exercise4_4Certification
-- name    : Kyprianou_Ch04_Exercise4_4Certification
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T22:33:55.101724+00:00
-- url     : https://prove2.me/theorems/6bc671b8-9724-4027-94ac-d9cbe8e96edf
-- title:
--   Kyprianou Chapter 4 Exercise 4.4 full completion certificate
-- statement:
--   The conjunction of all 1 textbook subparts of Exercise 4.4, each proposition reproduced from its source-matched Lean theorem telescope. No proposition is replaced by True or assumed proved.
-- source:
--   Kyprianou (2006), Chapter 4 Exercise 4.4, pp.105-109.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory ProbabilityTheory Filter ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04

noncomputable def certificate_ex4_4_main : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (phi : Real -> Real -> Omega -> Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
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
noncomputable def certificate_exercise_4_4 : Prop :=
    certificate_ex4_4_main

end Kyprianou.Ch04


