-- Prove2me | Definitions.Def_SourceProof_08d1eee1718e4902ecd9936c
-- name    : SourceProof_08d1eee1718e4902ecd9936c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:22:55.499142+00:00
-- url     : https://prove2.me/theorems/30886a0d-4254-4a1a-abe6-2f1f0f4847a5
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Poisson.exists_iSup_setLIntegral_timeSlab_le
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Time-simplicity of a Poisson random measure on a finite-intensity set

On a set of finite reference intensity the count of a Poisson random measure exceeds one with
probability at most the square of the intensity. The reference intensity is a product with
Lebesgue measure in time, so the masses of the dyadic time slabs of such a set are the integrals
of an integrable density over intervals of vanishing length, and therefore have vanishing
supremum. A union bound then makes the probability that some slab of level `n` carries two or
more points tend to zero, so almost surely no two points share a time and every point is simple.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Tail

end Tail

section Mesh


theorem _root_.Prove2MeSourceProof.h_08d1eee1718e4902ecd9936c {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hfin : ∫⁻ x, f x ≠ ⊤) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ n : ℕ, ⨆ k : ℕ, ∫⁻ x in timeSlab n k, f x ≤ ε := by
  set g : ℕ → ℝ → ℝ≥0∞ := fun M x => min (f x) (M : ℝ≥0∞) with hgdef
  have hgm : ∀ M, Measurable (g M) := fun M => hf.min measurable_const
  have hgle : ∀ M x, g M x ≤ f x := fun M x => min_le_left _ _
  have hgfin : ∀ M, ∫⁻ x, g M x ≠ ⊤ :=
    fun M => ne_top_of_le_ne_top hfin (lintegral_mono (hgle M))
  have hmono : Monotone g := fun a b hab x => min_le_min le_rfl (Nat.cast_le.mpr hab)
  have hpt : ∀ x : ℝ, ⨆ M : ℕ, g M x = f x := by
    intro x
    refine le_antisymm (iSup_le fun M => min_le_left _ _) ?_
    by_cases hx : f x = ⊤
    · have hgM : ∀ M : ℕ, g M x = (M : ℝ≥0∞) := by
        intro M
        simp only [hgdef]
        rw [hx, min_eq_right le_top]
      rw [hx, ← ENNReal.iSup_natCast]
      exact iSup_mono fun M => (hgM M).ge
    · obtain ⟨M, hM⟩ := ENNReal.exists_nat_gt hx
      exact le_iSup_of_le M (le_of_eq (min_eq_left hM.le).symm)
  have hsup : ⨆ M : ℕ, ∫⁻ x, g M x = ∫⁻ x, f x := by
    rw [← lintegral_iSup hgm hmono]
    exact lintegral_congr hpt
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (∫⁻ x, f x) - ∫⁻ x, g M x ≤ ε / 2 := by
    by_cases h0 : ∫⁻ x, f x = 0
    · exact ⟨0, by rw [h0]; simp⟩
    have hlt : (∫⁻ x, f x) - ε / 2 < ⨆ M : ℕ, ∫⁻ x, g M x := by
      rw [hsup]
      exact ENNReal.sub_lt_self hfin h0 (ENNReal.half_pos hε).ne'
    obtain ⟨M, hMlt⟩ := lt_iSup_iff.mp hlt
    refine ⟨M, ?_⟩
    rw [tsub_le_iff_right]
    calc ∫⁻ x, f x ≤ ((∫⁻ x, f x) - ε / 2) + ε / 2 := le_tsub_add
      _ ≤ (∫⁻ x, g M x) + ε / 2 := by gcongr
      _ = ε / 2 + ∫⁻ x, g M x := add_comm _ _
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (M : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) ≤ ε / 2 := by
    have hreal : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hE : Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hreal
    have hmul := ENNReal.Tendsto.const_mul hE (Or.inr (ENNReal.natCast_ne_top M))
    rw [mul_zero] at hmul
    exact ((ENNReal.tendsto_nhds_zero.mp hmul) (ε / 2) (ENNReal.half_pos hε)).exists
  refine ⟨n, iSup_le fun k => ?_⟩
  have hdecomp : ∫⁻ x in LevyStochCalc.Poisson.timeSlab n k, f x
      = (∫⁻ x in LevyStochCalc.Poisson.timeSlab n k, g M x) + ∫⁻ x in LevyStochCalc.Poisson.timeSlab n k, (f x - g M x) := by
    rw [← lintegral_add_left (hgm M) (fun x => f x - g M x)]
    exact lintegral_congr fun x => (add_tsub_cancel_of_le (hgle M x)).symm
  calc ∫⁻ x in LevyStochCalc.Poisson.timeSlab n k, f x
      = (∫⁻ x in LevyStochCalc.Poisson.timeSlab n k, g M x) + ∫⁻ x in LevyStochCalc.Poisson.timeSlab n k, (f x - g M x) := hdecomp
    _ ≤ (M : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) + ((∫⁻ x, f x) - ∫⁻ x, g M x) := by
        gcongr
        · calc ∫⁻ x in LevyStochCalc.Poisson.timeSlab n k, g M x
              ≤ ∫⁻ _ in LevyStochCalc.Poisson.timeSlab n k, (M : ℝ≥0∞) := lintegral_mono fun x => min_le_right _ _
            _ = (M : ℝ≥0∞) * volume (LevyStochCalc.Poisson.timeSlab n k) := by rw [setLIntegral_const]
            _ = (M : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by rw [LevyStochCalc.Poisson.volume_timeSlab]
        · calc ∫⁻ x in LevyStochCalc.Poisson.timeSlab n k, (f x - g M x)
              ≤ ∫⁻ x, (f x - g M x) := setLIntegral_le_lintegral _ _
            _ = (∫⁻ x, f x) - ∫⁻ x, g M x :=
                lintegral_sub (hgm M) (hgfin M) (Eventually.of_forall (hgle M))
    _ ≤ ε / 2 + ε / 2 := add_le_add hn hM
    _ = ε := ENNReal.add_halves ε
end Mesh

section Simple

end Simple

end LevyStochCalc.Poisson


