-- Prove2me | Definitions.Def_LevyStochCalc_Probability_Progressive_F001
-- name    : LevyStochCalc_Probability_Progressive_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:24:05.128853+00:00
-- url     : https://prove2.me/theorems/736e91ad-9b66-42f5-945c-fb15e6ce8dff
-- title:
--   Source declarations: LevyStochCalc.Probability.Progressive
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.Progressive. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
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

end ProgressivelyMeasurable

end General

section Mul

variable [TopologicalSpace E] [MulZeroClass E] [ContinuousMul E] {ℱ : Filtration ℝ mΩ}

/-- The pointwise product of two progressively measurable processes is progressively
measurable. -/
theorem ProgressivelyMeasurable.comp_continuous {A : Ω → ℝ → ℝ} {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hφ0 : φ 0 = 0) (hA : ProgressivelyMeasurable ℱ A) :
    ProgressivelyMeasurable ℱ fun ω s => φ (A ω s) := by
  intro t
  have heq : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => φ (A p.1 s)) p.2)
      = fun p : Ω × ℝ => φ ((Set.Iic t).indicator (A p.1) p.2) := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, hφ0]
  rw [heq]
  exact hφ.comp_stronglyMeasurable (hA t)
theorem ProgressivelyMeasurable.mul {A B : Ω → ℝ → E} (hA : ProgressivelyMeasurable ℱ A)
    (hB : ProgressivelyMeasurable ℱ B) :
    ProgressivelyMeasurable ℱ fun ω s => A ω s * B ω s := by
  intro t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => A p.1 s * B p.1 s) p.2)
      = fun p : Ω × ℝ =>
        (Set.Iic t).indicator (A p.1) p.2 * (Set.Iic t).indicator (B p.1) p.2 := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, zero_mul]
  rw [key]
  exact (hA t).mul (hB t)
end Mul

section Add

variable [NormedAddCommGroup E] {ℱ : Filtration ℝ mΩ}

/-- The pointwise sum of two progressively measurable processes is progressively measurable. -/
theorem ProgressivelyMeasurable.add {A B : Ω → ℝ → E} (hA : ProgressivelyMeasurable ℱ A)
    (hB : ProgressivelyMeasurable ℱ B) :
    ProgressivelyMeasurable ℱ fun ω s => A ω s + B ω s := by
  intro t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => A p.1 s + B p.1 s) p.2)
      = fun p : Ω × ℝ =>
        (Set.Iic t).indicator (A p.1) p.2 + (Set.Iic t).indicator (B p.1) p.2 := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, add_zero]
  rw [key]
  exact (hA t).add (hB t)
/-- The pointwise difference of two progressively measurable processes is progressively
measurable. -/
theorem ProgressivelyMeasurable.sub {A B : Ω → ℝ → E} (hA : ProgressivelyMeasurable ℱ A)
    (hB : ProgressivelyMeasurable ℱ B) :
    ProgressivelyMeasurable ℱ fun ω s => A ω s - B ω s := by
  intro t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => A p.1 s - B p.1 s) p.2)
      = fun p : Ω × ℝ =>
        (Set.Iic t).indicator (A p.1) p.2 - (Set.Iic t).indicator (B p.1) p.2 := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, sub_zero]
  rw [key]
  exact (hA t).sub (hB t)
end Add

section Integral

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {ℱ : Filtration ℝ mΩ} {H : Ω → ℝ → E}

/-- The integral of a progressively measurable process over a measurable set of times `≤ t`
is `ℱ t`-measurable. -/
theorem ProgressivelyMeasurable.stronglyMeasurable_setIntegral (h : ProgressivelyMeasurable ℱ H)
    {t : ℝ} {S : Set ℝ} (hS : MeasurableSet S) (hSt : S ⊆ Set.Iic t) (μ : Measure ℝ)
    [SFinite μ] : StronglyMeasurable[ℱ t] fun ω => ∫ s in S, H ω s ∂μ := by
  letI : MeasurableSpace Ω := ℱ t
  have h1 : StronglyMeasurable fun ω => ∫ s in S, (Set.Iic t).indicator (H ω) s ∂μ :=
    (h t).integral_prod_right' (ν := μ.restrict S)
  have : (fun ω => ∫ s in S, H ω s ∂μ)
      = fun ω => ∫ s in S, (Set.Iic t).indicator (H ω) s ∂μ := by
    funext ω
    exact setIntegral_congr_fun hS fun s hs => (Set.indicator_of_mem (hSt hs) _).symm
  rw [this]
  exact h1
end Integral

section Marked

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace F] [Zero F]

/-- A marked process `φ : Ω → ℝ → E → F` is progressively measurable for `ℱ` when, for every
time `t`, `(ω, s, e) ↦ φ ω s e` restricted to times `s ≤ t` (and `0` after `t`) is
`ℱ t ⊗ Borel ⊗ 𝓔`-measurable. -/
def MarkedProgressivelyMeasurable (ℱ : Filtration ℝ mΩ) (φ : Ω → ℝ → E → F) : Prop :=
  ∀ t : ℝ,
    @StronglyMeasurable (Ω × ℝ × E) F _
      (@Prod.instMeasurableSpace Ω (ℝ × E) (ℱ t) inferInstance)
      fun p : Ω × ℝ × E => (Set.Iic t).indicator (fun s => φ p.1 s p.2.2) p.2.1
namespace MarkedProgressivelyMeasurable

variable {ℱ : Filtration ℝ mΩ} {φ : Ω → ℝ → E → F}

/-- Composition with a continuous map fixing `0` preserves progressive measurability. -/
theorem _root_.Continuous.comp_markedProgressivelyMeasurable {G : Type*} [TopologicalSpace G]
    [Zero G] {g : F → G} (hg : Continuous g) (hg0 : g 0 = 0)
    (h : MarkedProgressivelyMeasurable ℱ φ) :
    MarkedProgressivelyMeasurable ℱ fun ω s e => g (φ ω s e) := by
  intro t
  have : (fun p : Ω × ℝ × E => (Set.Iic t).indicator (fun s => g (φ p.1 s p.2.2)) p.2.1)
      = fun p : Ω × ℝ × E => g ((Set.Iic t).indicator (fun s => φ p.1 s p.2.2) p.2.1) := by
    funext p
    exact congrFun (Set.indicator_comp_of_zero (f := fun s => φ p.1 s p.2.2)
      (s := Set.Iic t) hg0) p.2.1
  rw [this]
  exact hg.comp_stronglyMeasurable (h t)
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


