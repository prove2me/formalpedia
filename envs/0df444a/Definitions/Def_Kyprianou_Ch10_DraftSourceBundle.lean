-- Prove2me | Definitions.Def_Kyprianou_Ch10_DraftSourceBundle
-- name    : Kyprianou_Ch10_DraftSourceBundle
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:40:06.174771+00:00
-- url     : https://prove2.me/theorems/e2ed2bce-7654-4abc-b0ec-2414355af0fe
-- title:
--   Kyprianou Chapter 10 source model and historical declaration bundle
-- statement:
--   Source-checked Chapter 10 process, Levy mechanism, Lamperti clocks, state boundary conventions, historical certificates and the separate corrected conditional-law candidate. This bundle is Draft-only pending independent source equivalence and publication checks.

import Definitions.Def_Kyprianou_Ch10_Core06
open Filter Set ProbabilityTheory MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false
namespace Kyprianou.Ch10.StageE1
theorem firstNegative_positive_probability_of_levyLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (hLaw : Levy.HasLevyLaw X)
    (x : Time) (hx : 0 < x) :
    0 < X.law (x : ℝ)
      {ω : Ω | 0 < Levy.firstStrictNegative X.path ω} := by
  letI : IsProbabilityMeasure (X.law (x : ℝ)) := X.probability (x : ℝ)
  have hSubset :
      {ω : Ω | X.path 0 ω = (x : ℝ)} ⊆
      {ω : Ω | 0 < Levy.firstStrictNegative X.path ω} := by
    intro ω hω
    exact firstNegative_strictPositive_of_rightContinuous X
      hLaw ω x hx hω
  calc
    (0 : Mass) < 1 := by norm_num
    _ = X.law (x : ℝ)
      {ω : Ω | X.path 0 ω = (x : ℝ)} :=
        (X.initial (x : ℝ)).symm
    _ ≤ X.law (x : ℝ)
      {ω : Ω | 0 < Levy.firstStrictNegative X.path ω} :=
        measure_mono hSubset

theorem liftedLevy_clock_conditioning_denominator_positive
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (hLaw : Levy.HasLevyLaw X)
    (x q : Time) (hx : 0 < x) (hq : 0 < q) :
    0 < (liftPositiveJumpPaths X).law (x : ℝ)
      {p : Ω × ℝ |
        Levy.firstStrictNegative (liftPositiveJumpPaths X).path p >
          expClock q p} := by
  letI : IsProbabilityMeasure (X.law (x : ℝ)) := X.probability (x : ℝ)
  have hPositive :=
    firstNegative_positive_probability_of_levyLaw X hLaw x hx
  have hRectangle :=
    coupled_clock_survival_positive_of_lifetime
      (X.law (x : ℝ)) (Levy.firstStrictNegative X.path) q hq hPositive
  exact hRectangle

end Kyprianou.Ch10.StageE1


