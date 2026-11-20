-- Prove2me | Definitions.Def_SourceProof_74eb321e4a8b4ce4ef69f2c2
-- name    : SourceProof_74eb321e4a8b4ce4ef69f2c2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:19:50.900756+00:00
-- url     : https://prove2.me/theorems/f59da0c3-872e-41c4-91cd-fafe337e2469
-- title:
--   LevyStochCalc source module: SourceProof_74eb321e4a8b4ce4ef69f2c2
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.strictCount_eq` comes from the `LevyStochCalc.Poisson.StrictCount` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_StrictCount_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The strictly-past count of a Poisson random measure is predictable

The left endpoint of the level-`n` dyadic slab containing a positive time increases to that time
from strictly below, so the count of a set strictly before the time is the supremum over the
levels of the counts up to those endpoints. Each of those is a step process constant on the slabs
with a coefficient known at the left endpoint, hence predictable, and a countable supremum in the
extended nonnegative reals is measurable: the strictly-past count is predictable for every sample
point, with no null set involved.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Dyadic

end Dyadic

section Count

variable (N : PoissonRandomMeasure P ν)


theorem _root_.Prove2MeSourceProof.h_74eb321e4a8b4ce4ef69f2c2 {C : Set (ℝ × E)} {A : Set E} {T s : ℝ} (hs : 0 < s) (hsT : s ≤ T)
    {e : E} (he : e ∈ A) (ω : Ω) :
    strictCount N C A T ω s e = N.N ω (C ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ) := by
  have hmono : Monotone fun n : ℕ => C ∩ Set.Ioc (0 : ℝ) (LevyStochCalc.Poisson.dyadicLeft n s) ×ˢ Set.univ := by
    intro a b hab
    exact Set.inter_subset_inter_right _
      (Set.prod_mono (Set.Ioc_subset_Ioc_right (LevyStochCalc.Poisson.dyadicLeft_mono hs hab)) le_rfl)
  rw [LevyStochCalc.Poisson.strictCount]
  have hstep : ∀ n : ℕ, LevyStochCalc.Poisson.stepCount N C A T n ω s e
      = N.N ω (C ∩ Set.Ioc (0 : ℝ) (LevyStochCalc.Poisson.dyadicLeft n s) ×ˢ Set.univ) :=
    fun n => LevyStochCalc.Poisson.stepCount_eq N hs hsT he ω n
  simp_rw [hstep]
  rw [← hmono.measure_iUnion, ← Set.inter_iUnion, ← Set.iUnion_prod_const,
    LevyStochCalc.Poisson.iUnion_Ioc_dyadicLeft hs]
end Count

end LevyStochCalc.Poisson


