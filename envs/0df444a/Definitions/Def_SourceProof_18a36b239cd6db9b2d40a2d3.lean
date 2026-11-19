-- Prove2me | Definitions.Def_SourceProof_18a36b239cd6db9b2d40a2d3
-- name    : SourceProof_18a36b239cd6db9b2d40a2d3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:08:55.988662+00:00
-- url     : https://prove2.me/theorems/64402335-01c2-47f6-a684-dbb759af7fc2
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.ProgressivelyMeasurable.minTime
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


theorem _root_.Prove2MeSourceProof.h_18a36b239cd6db9b2d40a2d3 (h : ProgressivelyMeasurable ℱ H) (T : ℝ) :
    ProgressivelyMeasurable ℱ fun ω s => H ω (min s T) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hmono : ℱ (min t T) ≤ ℱ t := ℱ.mono (min_le_left t T)
  have hG : StronglyMeasurable fun q : Ω × ℝ => (Set.Iic (min t T)).indicator (H q.1) q.2 :=
    (h (min t T)).mono (sup_le_sup (MeasurableSpace.comap_mono hmono) le_rfl)
  have he : Measurable fun q : Ω × ℝ => ((q.1 : Ω), min q.2 T) :=
    measurable_fst.prodMk (measurable_snd.min measurable_const)
  have hcomp := hG.comp_measurable he
  have hind := hcomp.indicator (s := Set.univ ×ˢ Set.Iic t)
    (MeasurableSet.univ.prod measurableSet_Iic)
  have heq : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => H p.1 (min s T)) p.2)
      = (Set.univ ×ˢ Set.Iic t).indicator
        ((fun q : Ω × ℝ => (Set.Iic (min t T)).indicator (H q.1) q.2)
          ∘ fun q : Ω × ℝ => ((q.1 : Ω), min q.2 T)) := by
    funext p
    by_cases hp : p.2 ≤ t
    · have hmin : min p.2 T ≤ min t T := min_le_min hp le_rfl
      simp [hp, hmin, Function.comp_def]
    · simp [hp, Function.comp_def]
  rw [heq]
  exact hind
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


