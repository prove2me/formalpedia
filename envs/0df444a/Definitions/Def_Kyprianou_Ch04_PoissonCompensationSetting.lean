-- Prove2me | Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
-- name    : Kyprianou_Ch04_PoissonCompensationSetting
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T22:21:26.86091+00:00
-- url     : https://prove2.me/theorems/206e2596-613b-4fee-bcd1-d5cb61b47e2d
-- title:
--   Nonanticipating Poisson measure and predictable random kernel
-- statement:
--   A Poisson random measure is compatible with a filtration if all future marked interval counts are independent of the current past. A predictable kernel is nonnegative, jointly measurable, F_t-adapted in (omega,x), and almost surely left-continuous in time for each mark. These hypotheses do not include a compensation identity or martingale conclusion.
-- source:
--   Kyprianou (2006), first edition, Theorem 4.4, pp. 94-96.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04

/-- The counts on future time intervals are independent of the current
filtration. This excludes anticipating filtrations and does not assume a
compensation identity. -/
def IsFutureIndependentPoissonMeasure
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure) :
    Prop :=
  forall (u t : NNReal) (B : Set Real),
    u <= t -> MeasurableSet B ->
      Indep
        (MeasurableSpace.comap
          (fun omega : Omega =>
            N.N omega
              (Set.prod (Set.Ioc (u : Real) (t : Real)) B))
          inferInstance)
        (F u) P

/-- Joint measurability, F_t-adaptedness, nonnegativity and almost-sure
left-continuity from Kyprianou Theorem 4.4. -/
def IsAdmissiblePoissonKernel
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (phi : Real -> Real -> Omega -> Real) : Prop :=
  (forall s x omega, 0 <= phi s x omega) /\
  Measurable (fun z : (Real × Real) × Omega =>
    phi z.1.1 z.1.2 z.2) /\
  (forall t : NNReal,
    Measurable[(F t).prod inferInstance]
      (fun z : Omega × Real => phi (t : Real) z.2 z.1)) /\
  (forall x : Real, ∀ᵐ omega : Omega ∂P, forall t : NNReal,
    0 < t ->
      Tendsto (fun s : Real => phi s x omega)
        (nhdsWithin (t : Real) (Set.Iio (t : Real)))
        (nhds (phi (t : Real) x omega)))

end Kyprianou.Ch04


