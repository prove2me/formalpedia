-- Prove2me | Definitions.Def_SourceProof_27ffb6837c072f81fc480f19
-- name    : SourceProof_27ffb6837c072f81fc480f19
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:02:43.16435+00:00
-- url     : https://prove2.me/theorems/d0adc057-bc3c-4d24-a532-e3aec51cc5fe
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Ito.countable_setOf_pos_ne_of_cadlag
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpIntegrandLeftLim_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Integrands evaluated along the left limits of a path

A path in `ℝⁿ` that is right continuous on `[0, ∞)` and has left limits at every positive time
meets those left limits off a countable, hence Lebesgue null, set of times. An integrand
evaluated along such a path and the same integrand evaluated along a process that meets the path
at all but countably many positive times therefore agree almost everywhere for the product of the
sample measure, Lebesgue measure on the horizon and the mark measure, so the compensated integral
takes the same value on the two integrands; the same null set serves the iterated integral
against the mark measure and Lebesgue measure and the integral against the reference intensity.

The identification is one of `L²` classes: it concerns the compensated integral constructed from
the energy isometry, not a pathwise Stieltjes integral against the jump measure, for which the
two conventions differ.

## Main statements

* `countable_setOf_pos_ne_of_cadlag` — a path right continuous on `[0, ∞)` differs from its left
  limits at only countably many positive times.
* `compensatedIntegral_congr_of_countable_ne` — the compensated integrals of an integrand
  evaluated along two processes meeting at all but countably many positive times agree almost
  surely.
* `setIntegral_congr_of_countable_ne` and
  `setIntegral_referenceIntensity_congr_of_countable_ne` — the same for the compensator drift
  term, in its iterated and its product-measure form.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito

universe u v w

section Cadlag

variable {n : ℕ}


theorem _root_.Prove2MeSourceProof.h_27ffb6837c072f81fc480f19 {f g : ℝ → Fin n → ℝ}
    (hright : ∀ t : ℝ, 0 ≤ t → Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (hleft : ∀ t : ℝ, 0 < t → ∀ i : Fin n,
      Tendsto (fun s => f s i) (𝓝[<] t) (𝓝 (g t i))) :
    {t : ℝ | 0 < t ∧ f t ≠ g t}.Countable := by
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → Fin n → ℝ, ∀ s : ℝ, F s = f (max s 0) :=
    ⟨fun s => f (max s 0), fun _ => rfl⟩
  have hFpos : ∀ s : ℝ, 0 < s → F s = f s := by
    intro s hs
    rw [hFdef s, max_eq_left hs.le]
  have hFnonpos : ∀ s : ℝ, s ≤ 0 → F s = f 0 := by
    intro s hs
    rw [hFdef s, max_eq_right hs]
  have hFright : ∀ t : ℝ, Tendsto F (𝓝[>] t) (𝓝 (F t)) := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · have hFt : F t = f t := by rw [hFdef t, max_eq_left ht]
      have hev : (fun s => f s) =ᶠ[𝓝[>] t] F := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (hFpos s (lt_of_le_of_lt ht hs)).symm
      rw [hFt]
      exact (hright t ht).congr' hev
    · have hFt : F t = f 0 := hFnonpos t ht.le
      have hev : (fun _ : ℝ => f 0) =ᶠ[𝓝[>] t] F := by
        filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ht)] with s hs
        exact (hFnonpos s hs.le).symm
      rw [hFt]
      exact tendsto_const_nhds.congr' hev
  have hFleftPos : ∀ t : ℝ, 0 < t → ∀ i : Fin n,
      Tendsto (fun s => F s i) (𝓝[<] t) (𝓝 (g t i)) := by
    intro t ht i
    have hev : (fun s => f s i) =ᶠ[𝓝[<] t] fun s => F s i := by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ht)] with s hs
      rw [hFpos s hs]
    exact (hleft t ht i).congr' hev
  have hFleft : ∀ (t : ℝ) (i : Fin n), ∃ L : ℝ, Tendsto (fun s => F s i) (𝓝[<] t) (𝓝 L) := by
    intro t i
    rcases le_or_gt t 0 with ht | ht
    · refine ⟨f 0 i, ?_⟩
      have hev : (fun _ : ℝ => f 0 i) =ᶠ[𝓝[<] t] fun s => F s i := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        rw [hFnonpos s (le_of_lt (lt_of_lt_of_le hs ht))]
      exact tendsto_const_nhds.congr' hev
    · exact ⟨g t i, hFleftPos t ht i⟩
  refine Set.Countable.mono ?_ (LevyStochCalc.Ito.countable_setOf_ne_leftLim_pi hFright hFleft)
  intro t ht
  obtain ⟨htpos, htne⟩ := ht
  simp only [Set.mem_setOf_eq]
  intro hEq
  refine htne ?_
  have hgl : ∀ i : Fin n, Function.leftLim (fun s => F s i) t = g t i := fun i =>
    leftLim_eq_of_tendsto (hFleftPos t htpos i)
  have hft : f t = fun i => Function.leftLim (fun s => F s i) t := by
    rw [← hFpos t htpos]
    exact hEq
  rw [hft]
  funext i
  exact hgl i
end Cadlag

section Horizon

end Horizon

section Integrand

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {V : Type w}
  {P : Measure Ω}

end Integrand

section Compensated

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {V : Type w}
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

end Compensated

section Drift

variable {Ω : Type u} {E : Type v} [MeasurableSpace E] {V : Type w}

end Drift

end LevyStochCalc.Ito


