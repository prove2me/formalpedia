-- Prove2me | Definitions.Def_SourceProof_07135226a3b6eb1d82b734e1
-- name    : SourceProof_07135226a3b6eb1d82b734e1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:20:31.356596+00:00
-- url     : https://prove2.me/theorems/ceb75382-7f86-4e18-8bc1-92f64bc6eb89
-- title:
--   LevyStochCalc source module: SourceProof_07135226a3b6eb1d82b734e1
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.ae_count_time_singleton_le_one` comes from the `LevyStochCalc.Poisson.Simplicity` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F000
import Definitions.Def_SourceProof_e5991b7ae0d55e70e03866a8
import Definitions.Def_SourceProof_fb5deb26889ca539bc17760c

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

end Mesh

section Simple


theorem _root_.Prove2MeSourceProof.h_07135226a3b6eb1d82b734e1 (N : PoissonRandomMeasure.{u, v, w} P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, N.N ω (B ∩ {s} ×ˢ Set.univ) ≤ 1 := by
  filter_upwards [_root_.Prove2MeSourceProof.h_fb5deb26889ca539bc17760c N hB hfin,
    LevyStochCalc.Poisson.ae_count_Iic_zero_eq_zero N hB] with ω hω h0 s
  obtain ⟨n, hn⟩ := hω
  rcases le_or_gt s 0 with hs | hs
  · calc N.N ω (B ∩ {s} ×ˢ Set.univ)
        ≤ N.N ω (B ∩ Set.Iic (0 : ℝ) ×ˢ Set.univ) :=
          measure_mono (Set.inter_subset_inter_right _
            (Set.prod_mono (Set.singleton_subset_iff.mpr (Set.mem_Iic.mpr hs)) le_rfl))
      _ = 0 := h0
      _ ≤ 1 := bot_le
  · have hmem : s ∈ ⋃ k : ℕ, LevyStochCalc.Poisson.timeSlab n k := by
      rw [_root_.Prove2MeSourceProof.h_e5991b7ae0d55e70e03866a8]
      exact hs
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
    refine le_trans (measure_mono ?_) (hn k)
    exact Set.inter_subset_inter_right _
      (Set.prod_mono (Set.singleton_subset_iff.mpr hk) le_rfl)
end Simple

end LevyStochCalc.Poisson


