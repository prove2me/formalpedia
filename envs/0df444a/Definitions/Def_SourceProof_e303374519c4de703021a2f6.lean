-- Prove2me | Definitions.Def_SourceProof_e303374519c4de703021a2f6
-- name    : SourceProof_e303374519c4de703021a2f6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:08:39.657188+00:00
-- url     : https://prove2.me/theorems/5deb0629-f276-45ae-bebc-e93f5baa6622
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.ProgressivelyMeasurable.isStronglyProgressive
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Progressive_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Progressively measurable real processes

`ProgressivelyMeasurable ℱ H` says that the process `H : Ω → ℝ → E`, viewed as a function of
`(ω, s)`, is `ℱ t ⊗ Borel`-measurable on the time window `s ≤ t`, for every `t`. This is
the progressive measurability of Mathlib's `IsStronglyProgressive`, phrased on `Ω × ℝ` by
truncating the time variable at `t`, which is the form in which the stochastic integrals of
this library consume it; `isStronglyProgressive` and `of_isStronglyProgressive` relate the
two.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω}

section General

variable [TopologicalSpace E] [Zero E] [TopologicalSpace F] [Zero F]

namespace ProgressivelyMeasurable

variable {ℱ : Filtration ℝ mΩ} {H : Ω → ℝ → E}


theorem _root_.Prove2MeSourceProof.h_e303374519c4de703021a2f6 (h : ProgressivelyMeasurable ℱ H) :
    IsStronglyProgressive ℱ fun s ω => H ω s := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have he : Measurable fun q : Set.Iic t × Ω => (q.2, (q.1 : ℝ)) :=
    measurable_snd.prodMk (measurable_subtype_coe.comp measurable_fst)
  have := (h t).comp_measurable he
  have heq : (fun q : Set.Iic t × Ω => H q.2 q.1)
      = (fun p : Ω × ℝ => (Set.Iic t).indicator (H p.1) p.2) ∘ fun q : Set.Iic t × Ω =>
        (q.2, (q.1 : ℝ)) := by
    funext q
    exact (Set.indicator_of_mem q.1.2 _).symm
  rw [heq]
  exact this
end ProgressivelyMeasurable

end General

section Mul

variable [TopologicalSpace E] [MulZeroClass E] [ContinuousMul E] {ℱ : Filtration ℝ mΩ}

end Mul

section Add

variable [NormedAddCommGroup E] {ℱ : Filtration ℝ mΩ}

end Add

section Integral

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {ℱ : Filtration ℝ mΩ} {H : Ω → ℝ → E}

end Integral

section Marked

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace F] [Zero F]

namespace MarkedProgressivelyMeasurable

variable {ℱ : Filtration ℝ mΩ} {φ : Ω → ℝ → E → F}

end MarkedProgressivelyMeasurable

end Marked

section MarkedIntegral

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ℱ : Filtration ℝ mΩ} {φ : Ω → ℝ → E → F}

end MarkedIntegral

/-! ### Countable suprema of real progressively measurable processes -/

section RealLimsup

variable {ℱ : Filtration ℝ mΩ}

end RealLimsup

end LevyStochCalc.Probability


