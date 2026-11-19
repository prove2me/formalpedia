-- Prove2me | Definitions.Def_LevyStochCalc_Probability_Progressive_F000
-- name    : LevyStochCalc_Probability_Progressive_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:07:21.251246+00:00
-- url     : https://prove2.me/theorems/ed8b03bc-c4ea-4486-ae02-0b67e42d7562
-- title:
--   Source declarations: LevyStochCalc.Probability.Progressive
-- statement:
--   Source-preserving Lean declaration bundle from LevyStochCalc.Probability.Progressive, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Process.Adapted

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

/-- The process `H` is progressively measurable for `ℱ`: for every time `t`, the map
`(ω, s) ↦ H ω s` restricted to times `s ≤ t` (and `0` after `t`) is
`ℱ t ⊗ Borel`-measurable. -/
def ProgressivelyMeasurable (ℱ : Filtration ℝ mΩ) (H : Ω → ℝ → E) : Prop :=
  ∀ t : ℝ,
    @StronglyMeasurable (Ω × ℝ) E _ (@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance)
      fun p : Ω × ℝ => (Set.Iic t).indicator (H p.1) p.2
namespace ProgressivelyMeasurable

variable {ℱ : Filtration ℝ mΩ} {H : Ω → ℝ → E}

/-- A progressively measurable process is adapted. -/
theorem stronglyMeasurable_eval (h : ProgressivelyMeasurable ℱ H) (t : ℝ) :
    StronglyMeasurable[ℱ t] fun ω => H ω t := by
  letI : MeasurableSpace Ω := ℱ t
  have := (h t).comp_measurable (measurable_prodMk_right (y := t))
  simpa [Function.comp_def] using this
/-- Composition with a continuous map fixing `0` preserves progressive measurability. -/
theorem _root_.Continuous.comp_progressivelyMeasurable {φ : E → F} (hφ : Continuous φ)
    (hφ0 : φ 0 = 0) (h : ProgressivelyMeasurable ℱ H) :
    ProgressivelyMeasurable ℱ fun ω s => φ (H ω s) := by
  intro t
  have : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => φ (H p.1 s)) p.2)
      = fun p : Ω × ℝ => φ ((Set.Iic t).indicator (H p.1) p.2) := by
    funext p
    exact congrFun (Set.indicator_comp_of_zero (f := H p.1) (s := Set.Iic t) hφ0) p.2
  rw [this]
  exact hφ.comp_stronglyMeasurable (h t)
/-- Progressive measurability is monotone in the filtration. -/
theorem mono {𝒢 : Filtration ℝ mΩ} (h : ProgressivelyMeasurable ℱ H)
    (hle : ∀ t, ℱ t ≤ 𝒢 t) : ProgressivelyMeasurable 𝒢 H := fun t =>
  (h t).mono (sup_le_sup (MeasurableSpace.comap_mono (hle t)) le_rfl)
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


