-- Prove2me | Definitions.Def_SourceProof_010d482425efb705a03802af
-- name    : SourceProof_010d482425efb705a03802af
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:39:13.734478+00:00
-- url     : https://prove2.me/theorems/603b0d75-4e11-485e-8871-9c4d21f742eb
-- title:
--   LevyStochCalc source module: SourceProof_010d482425efb705a03802af
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.IsRectSimple.eq_finSum` comes from the `LevyStochCalc.Poisson.CompensatedDensityRectSimple` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRectSimple_F000

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


theorem _root_.Prove2MeSourceProof.h_010d482425efb705a03802af {g : Ω × E → ℝ} (hg : IsRectSimple g) :
    ∃ (K : ℕ) (a : Fin K → ℝ) (A : Fin K → Set Ω) (B : Fin K → Set E),
      (∀ k, MeasurableSet (A k)) ∧ (∀ k, MeasurableSet (B k)) ∧
      (∀ ω e, g (ω, e) = ∑ k : Fin K, a k * (A k).indicator (fun _ => (1 : ℝ)) ω
                              * (B k).indicator (fun _ => (1 : ℝ)) e) := by
  classical
  obtain ⟨L, hL, hgeq⟩ := hg
  refine ⟨L.length, fun k => (L.get k).1, fun k => (L.get k).2.1, fun k => (L.get k).2.2,
    fun k => (hL (L.get k) (List.get_mem L k)).1,
    fun k => (hL (L.get k) (List.get_mem L k)).2, ?_⟩
  intro ω e
  rw [hgeq]
  change (L.map (fun t => t.1 * (t.2.1 ×ˢ t.2.2).indicator (fun _ => (1 : ℝ)) (ω, e))).sum = _
  rw [← List.ofFn_getElem_eq_map L
        (fun t => t.1 * (t.2.1 ×ˢ t.2.2).indicator (fun _ => (1 : ℝ)) (ω, e)),
      Fin.sum_ofFn]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [List.get_eq_getElem]
  rw [show ((L[(k : ℕ)]).2.1 ×ˢ (L[(k : ℕ)]).2.2).indicator (fun _ => (1 : ℝ)) (ω, e)
        = ((L[(k : ℕ)]).2.1).indicator (fun _ => (1 : ℝ)) ω
          * ((L[(k : ℕ)]).2.2).indicator (fun _ => (1 : ℝ)) e from by
    by_cases hω : ω ∈ (L[(k : ℕ)]).2.1 <;> by_cases he : e ∈ (L[(k : ℕ)]).2.2 <;>
      simp [Set.mem_prod, hω, he]]
  ring
end LevyStochCalc.Poisson.Compensated


