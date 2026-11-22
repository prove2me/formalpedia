-- Prove2me | Definitions.Def_SourceProof_1c19127385342f00e6ef4903
-- name    : SourceProof_1c19127385342f00e6ef4903
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:27:55.098474+00:00
-- url     : https://prove2.me/theorems/16bb1be4-e035-4237-a139-cacc108fe6b2
-- title:
--   LevyStochCalc source module: SourceProof_1c19127385342f00e6ef4903
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub_shift` comes from the `LevyStochCalc.Ito.JumpFormulaChainStopped` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_c06e7c5484d0e8d23b1df1b4

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

end ShiftRegion

section StoppedShift

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {n : ℕ} {ℱ : Filtration ℝ mΩ}
  {σ τ : Ω → WithTop ℝ}


theorem _root_.Prove2MeSourceProof.h_1c19127385342f00e6ef4903 (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (hστ : ∀ ω, σ ω ≤ τ ω)
    {c : Ω → Fin n → ℝ} (hc : Measurable[hσ.measurableSpace] c)
    {V : ℝ → Ω → Fin n → ℝ} (hV : Probability.ProgressivelyMeasurable ℱ fun ω s => V s ω)
    {φ : (Fin n → ℝ) → ℝ} (hφ : Continuous φ) {H : Ω → ℝ → ℝ}
    (hH : Probability.ProgressivelyMeasurable ℱ H) {K : Ω → ℝ → ℝ}
    (hK : ∀ ω s, K ω s = φ (V s ω + c ω) * H ω s) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ K ω s - Probability.stopped σ K ω s := by
  intro t
  set mt : MeasurableSpace (Ω × ℝ) := @Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance with hmt
  set U : Set (Ω × ℝ) := {p : Ω × ℝ | σ p.1 < ((p.2 : ℝ) : WithTop ℝ) ∧ p.2 ≤ t} with hUdef
  have hind : Measurable[mt] (Set.indicator U fun p : Ω × ℝ => c p.1) :=
    _root_.Prove2MeSourceProof.h_c06e7c5484d0e8d23b1df1b4 hσ hc t
  have hVm : Measurable[mt] fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => V s p.1) p.2 :=
    (hV t).measurable
  have hHm : Measurable[mt] fun p : Ω × ℝ => (Set.Iic t).indicator (H p.1) p.2 :=
    (hH t).measurable
  have hw : Measurable[mt] fun p : Ω × ℝ =>
      (LevyStochCalc.Probability.stoppedRegion τ t).indicator (fun _ => (1 : ℝ)) p
        - (LevyStochCalc.Probability.stoppedRegion σ t).indicator (fun _ => (1 : ℝ)) p :=
    (measurable_const.indicator (_root_.Prove2MeSourceProof.h_0efef36d22ac9421e0560dc4 hτ t)).sub
      (measurable_const.indicator (_root_.Prove2MeSourceProof.h_0efef36d22ac9421e0560dc4 hσ t))
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator
        (fun s => LevyStochCalc.Probability.stopped τ K p.1 s - LevyStochCalc.Probability.stopped σ K p.1 s) p.2)
      = fun p : Ω × ℝ =>
        ((LevyStochCalc.Probability.stoppedRegion τ t).indicator (fun _ => (1 : ℝ)) p
            - (LevyStochCalc.Probability.stoppedRegion σ t).indicator (fun _ => (1 : ℝ)) p)
          * φ ((Set.Iic t).indicator (fun s => V s p.1) p.2
              + Set.indicator U (fun p : Ω × ℝ => c p.1) p)
          * (Set.Iic t).indicator (H p.1) p.2 := by
    funext p
    by_cases hp : p.2 ≤ t
    · have hpI : p.2 ∈ Set.Iic t := Set.mem_Iic.mpr hp
      rw [Set.indicator_of_mem hpI (fun s => LevyStochCalc.Probability.stopped τ K p.1 s
          - LevyStochCalc.Probability.stopped σ K p.1 s), Set.indicator_of_mem hpI (H p.1),
        Set.indicator_of_mem hpI (fun s => V s p.1)]
      by_cases hσp : ((p.2 : ℝ) : WithTop ℝ) ≤ σ p.1
      · have hτp : ((p.2 : ℝ) : WithTop ℝ) ≤ τ p.1 := hσp.trans (hστ p.1)
        rw [Set.indicator_of_mem (show p ∈ LevyStochCalc.Probability.stoppedRegion τ t from ⟨hp, hτp⟩),
          Set.indicator_of_mem (show p ∈ LevyStochCalc.Probability.stoppedRegion σ t from ⟨hp, hσp⟩),
          LevyStochCalc.Probability.stopped, LevyStochCalc.Probability.stopped, if_pos hτp, if_pos hσp]
        ring
      · have hσlt : σ p.1 < ((p.2 : ℝ) : WithTop ℝ) := not_le.mp hσp
        rw [Set.indicator_of_notMem (show p ∉ LevyStochCalc.Probability.stoppedRegion σ t from
          fun h => hσp h.2)]
        by_cases hτp : ((p.2 : ℝ) : WithTop ℝ) ≤ τ p.1
        · rw [Set.indicator_of_mem (show p ∈ LevyStochCalc.Probability.stoppedRegion τ t from ⟨hp, hτp⟩),
            Set.indicator_of_mem (show p ∈ U from ⟨hσlt, hp⟩),
            LevyStochCalc.Probability.stopped, LevyStochCalc.Probability.stopped, if_pos hτp,
            if_neg (not_le.mpr hσlt), hK p.1 p.2]
          ring
        · rw [Set.indicator_of_notMem (show p ∉ LevyStochCalc.Probability.stoppedRegion τ t from
            fun h => hτp h.2), LevyStochCalc.Probability.stopped, LevyStochCalc.Probability.stopped, if_neg hτp,
            if_neg (not_le.mpr hσlt)]
          ring
    · have hpI : p.2 ∉ Set.Iic t := fun h => hp (Set.mem_Iic.mp h)
      rw [Set.indicator_of_notMem hpI (fun s => LevyStochCalc.Probability.stopped τ K p.1 s
          - LevyStochCalc.Probability.stopped σ K p.1 s), Set.indicator_of_notMem hpI (H p.1)]
      ring
  rw [key]
  exact ((hw.mul (hφ.measurable.comp (hVm.add hind))).mul hHm).stronglyMeasurable
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


