-- Prove2me | Definitions.Def_SourceProof_c06e7c5484d0e8d23b1df1b4
-- name    : SourceProof_c06e7c5484d0e8d23b1df1b4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:23:31.269535+00:00
-- url     : https://prove2.me/theorems/c1f6712d-b24b-4d29-96a8-4b625ac9a125
-- title:
--   LevyStochCalc source module: SourceProof_c06e7c5484d0e8d23b1df1b4
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.measurable_indicator_shiftRegion` comes from the `LevyStochCalc.Ito.JumpFormulaChainStopped` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CappedJumpSumMeasurable_F001
import Definitions.Def_SourceProof_0efef36d22ac9421e0560dc4

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Increments read along a random vector known at the earlier stopping time

The increment between two ordered stopping times of an integrand built from a path translated by
a random vector known at the earlier time is supported on the region strictly after that time,
where the translation is already known: there the translated path is the path plus the cut-off
vector, which is measurable for the σ-algebra at the running time because the region is a
countable union of rectangles `{σ ≤ q} × (q, t]`. The increment is therefore progressively
measurable without any restriction on the range of the vector or on that of the stopping times.

## Main statements

* `LevyStochCalc.Brownian.Ito.measurable_indicator_shiftRegion` — a random vector known at a
  stopping time, cut to the times strictly after it and up to a horizon, is measurable for the
  σ-algebra at that horizon on the product with the time axis.
* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub_shift` — the increment between
  two ordered stopping times of an integrand read along a random vector known at the earlier one
  is progressively measurable.
* `LevyStochCalc.Brownian.Ito.measurable_uncurry_stopped_sub_shift` — that increment has
  measurable uncurrying.
* `LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_stopped_sub_cappedJumpSumAt` — the
  increment between consecutive capped arrival times of an integrand read along the capped
  left-limit jump sum is progressively measurable.
* `LevyStochCalc.Ito.JumpFormula.measurable_uncurry_stopped_sub_cappedJumpSumAt` — that
  increment has measurable uncurrying.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory

universe u v

section ShiftRegion

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type*} [MeasurableSpace E] [Zero E]
  {ℱ : Filtration ℝ mΩ} {σ : Ω → WithTop ℝ}


theorem _root_.Prove2MeSourceProof.h_c06e7c5484d0e8d23b1df1b4 (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    {c : Ω → E} (hc : Measurable[hσ.measurableSpace] c) (t : ℝ) :
    Measurable[@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance]
      (Set.indicator {p : Ω × ℝ | σ p.1 < ((p.2 : ℝ) : WithTop ℝ) ∧ p.2 ≤ t}
        fun p => c p.1) := by
  letI : MeasurableSpace Ω := ℱ t
  set U : Set (Ω × ℝ) := {p : Ω × ℝ | σ p.1 < ((p.2 : ℝ) : WithTop ℝ) ∧ p.2 ≤ t} with hUdef
  have hU : MeasurableSet U := by
    have heq : U = (Set.univ ×ˢ Set.Iic t) \ LevyStochCalc.Probability.stoppedRegion σ t := by
      ext p
      simp only [hUdef, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_prod, Set.mem_univ, Set.mem_Iic,
        true_and, LevyStochCalc.Probability.mem_stoppedRegion, not_and, not_le]
      exact ⟨fun h => ⟨h.2, fun _ => h.1⟩, fun h => ⟨h.2 h.1, h.1⟩⟩
    rw [heq]
    exact (MeasurableSet.univ.prod measurableSet_Iic).diff
      (_root_.Prove2MeSourceProof.h_0efef36d22ac9421e0560dc4 hσ t)
  intro B hB
  have hUB : MeasurableSet (U ∩ (fun p : Ω × ℝ => c p.1) ⁻¹' B) := by
    have hcov : U ∩ (fun p : Ω × ℝ => c p.1) ⁻¹' B
        = ⋃ q : ℚ, (c ⁻¹' B ∩ {ω : Ω | σ ω ≤ ((min (q : ℝ) t : ℝ) : WithTop ℝ)})
            ×ˢ (Set.Ioi (q : ℝ) ∩ Set.Iic t) := by
      ext p
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        have hne : σ p.1 ≠ ⊤ := by
          intro htop
          rw [htop] at h1
          exact absurd h1 (by simp)
        obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
        rw [← hr] at h1
        have hrlt : r < p.2 := by exact_mod_cast h1
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hrlt
        refine Set.mem_iUnion.mpr ⟨q, ⟨h3, ?_⟩, hq2, h2⟩
        change σ p.1 ≤ ((min (q : ℝ) t : ℝ) : WithTop ℝ)
        rw [← hr]
        have hmin : r ≤ min (q : ℝ) t := le_min hq1.le (hq1.le.trans (hq2.le.trans h2))
        exact_mod_cast hmin
      · intro hmem
        obtain ⟨q, ⟨h3, h4⟩, h5, h6⟩ := Set.mem_iUnion.mp hmem
        refine ⟨⟨?_, h6⟩, h3⟩
        calc σ p.1 ≤ ((min (q : ℝ) t : ℝ) : WithTop ℝ) := h4
          _ ≤ ((q : ℝ) : WithTop ℝ) := by exact_mod_cast min_le_left (q : ℝ) t
          _ < ((p.2 : ℝ) : WithTop ℝ) := by exact_mod_cast h5
    rw [hcov]
    refine MeasurableSet.iUnion fun q => MeasurableSet.prod ?_ ?_
    · exact (ℱ.mono (min_le_right (q : ℝ) t)) _ ((hc hB).2 (min (q : ℝ) t))
    · exact measurableSet_Ioi.inter measurableSet_Iic
  by_cases h0 : (0 : E) ∈ B
  · have hpre : (Set.indicator U fun p : Ω × ℝ => c p.1) ⁻¹' B
        = (U ∩ (fun p : Ω × ℝ => c p.1) ⁻¹' B) ∪ Uᶜ := by
      ext p
      by_cases hp : p ∈ U <;> simp [hp, h0]
    rw [hpre]
    exact hUB.union hU.compl
  · have hpre : (Set.indicator U fun p : Ω × ℝ => c p.1) ⁻¹' B
        = U ∩ (fun p : Ω × ℝ => c p.1) ⁻¹' B := by
      ext p
      by_cases hp : p ∈ U <;> simp [hp, h0]
    rw [hpre]
    exact hUB
end ShiftRegion

section StoppedShift

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {n : ℕ} {ℱ : Filtration ℝ mΩ}
  {σ τ : Ω → WithTop ℝ}

end StoppedShift

section FromUnstopped

open scoped NNReal ENNReal

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {n d : ℕ} {ℱ : Filtration ℝ mΩ}
  {P : Measure Ω} [IsProbabilityMeasure P] {chain : ℕ → Ω → WithTop ℝ}
  {V : ℝ → Ω → Fin n → ℝ} {c : ℕ → Ω → Fin n → ℝ} {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}

end FromUnstopped

end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Ito.JumpFormula

open MeasureTheory ProbabilityTheory Filter Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {A : Set E}

end LevyStochCalc.Ito.JumpFormula


