-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRectSimple_F000
-- name    : LevyStochCalc_Poisson_CompensatedDensityRectSimple_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T20:55:20.886262+00:00
-- url     : https://prove2.me/theorems/48d9acec-2f4f-4f1a-a14c-7e93f9d3b68f
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityRectSimple
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityRectSimple. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityShifted_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Rectangle-simple functions and their `L²` density

Finite `ℝ`-linear combinations of indicators of measurable rectangles `A ×ˢ B ⊆ Ω × E`, their
closure properties, and their density in `L²(μ)` for a finite measure `μ` on `Ω × E`. The
density is obtained from the monotone-class theorem over the rectangle π-system, so no countable
generation or standard-Borel hypothesis on `E` is required; a trimmed-product lemma transfers
`L²` bounds along a sub-σ-algebra of `Ω`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Mark discretisation via rectangle density (general `E`)

To turn the (mark-continuous) shifted dyadic eval into a genuine `SimplePredictable`,
we approximate the mark dependence by `ℝ`-linear combinations of indicators of
measurable rectangles `A ×ˢ B`. These are dense in `L²(μΩ ⊗ μE)` for *finite*
measures by the monotone-class theorem over the rectangle π-system
(`isPiSystem_prod`/`generateFrom_prod`) — **no countable-generation/standard-Borel
on `E` is needed**. -/

/-- A finite `ℝ`-linear combination of indicators of measurable rectangles
`A ×ˢ B ⊆ Ω × E`. -/
def IsRectSimple (g : Ω × E → ℝ) : Prop :=
  ∃ L : List (ℝ × Set Ω × Set E),
    (∀ t ∈ L, MeasurableSet t.2.1 ∧ MeasurableSet t.2.2) ∧
    g = fun x => (L.map (fun t => t.1 * (t.2.1 ×ˢ t.2.2).indicator (fun _ => (1 : ℝ)) x)).sum
/-- The zero function is rectangle-simple (empty combination). -/
lemma IsRectSimple.zero : IsRectSimple (fun _ : Ω × E => (0 : ℝ)) :=
  ⟨[], by simp, by funext x; simp⟩
/-- The indicator of a measurable rectangle is rectangle-simple. -/
lemma IsRectSimple.rect {A : Set Ω} {B : Set E} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    IsRectSimple (fun x : Ω × E => (A ×ˢ B).indicator (fun _ => (1 : ℝ)) x) := by
  refine ⟨[(1, A, B)], by simp [hA, hB], ?_⟩
  funext x; simp
/-- Rectangle-simple functions are closed under addition (list concatenation). -/
lemma IsRectSimple.add {g h : Ω × E → ℝ} (hg : IsRectSimple g) (hh : IsRectSimple h) :
    IsRectSimple (g + h) := by
  obtain ⟨L₁, hL₁, hgeq⟩ := hg
  obtain ⟨L₂, hL₂, hheq⟩ := hh
  refine ⟨L₁ ++ L₂, ?_, ?_⟩
  · intro t ht; rcases List.mem_append.mp ht with h' | h'
    exacts [hL₁ t h', hL₂ t h']
  · funext x; simp only [Pi.add_apply, hgeq, hheq, List.map_append, List.sum_append]
/-- Rectangle-simple functions are closed under scalar multiplication. -/
lemma IsRectSimple.smul {g : Ω × E → ℝ} (hg : IsRectSimple g) (c : ℝ) :
    IsRectSimple (fun x => c * g x) := by
  obtain ⟨L, hL, hgeq⟩ := hg
  refine ⟨L.map (fun t => (c * t.1, t.2.1, t.2.2)), ?_, ?_⟩
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    exact hL t' ht'
  · funext x
    simp only [hgeq]
    clear hgeq hL
    induction L with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [mul_add, ih]; ring
/-- A rectangle-simple function is measurable. -/
lemma IsRectSimple.measurable {g : Ω × E → ℝ} (hg : IsRectSimple g) : Measurable g := by
  obtain ⟨L, hL, rfl⟩ := hg
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil]; exact measurable_const
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons]
    have ht := hL t (List.mem_cons_self)
    refine Measurable.add ?_ (ih (fun s hs => hL s (List.mem_cons_of_mem t hs)))
    exact measurable_const.mul (measurable_const.indicator (ht.1.prod ht.2))
/-- Rectangle-simple functions are a.e.-strongly-measurable for any measure. -/
lemma IsRectSimple.aestronglyMeasurable {g : Ω × E → ℝ} (hg : IsRectSimple g)
    (μ : Measure (Ω × E)) : MeasureTheory.AEStronglyMeasurable g μ :=
  hg.measurable.aestronglyMeasurable
/-- Rectangle-simple functions are closed under finite sums. -/
lemma IsRectSimple.sum {ι : Type*} (s : Finset ι) (f : ι → Ω × E → ℝ)
    (h : ∀ i ∈ s, IsRectSimple (f i)) : IsRectSimple (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact IsRectSimple.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
/-- `f` is approximable in `L²(μ)` by rectangle-simple functions. -/
def RectApprox (μ : Measure (Ω × E)) (f : Ω × E → ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ g, IsRectSimple g ∧ MeasureTheory.eLpNorm (f - g) 2 μ < ε
end LevyStochCalc.Poisson.Compensated


