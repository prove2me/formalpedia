-- Prove2me | Definitions.Def_SourceProof_14a201cfcde1fac50a3f98f3
-- name    : SourceProof_14a201cfcde1fac50a3f98f3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:51:28.625101+00:00
-- url     : https://prove2.me/theorems/5bd70e49-5c6e-4f34-b26a-448a5eae2945
-- title:
--   LevyStochCalc source module: SourceProof_14a201cfcde1fac50a3f98f3
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Continuity.exists_tendsto_of_local_holder` comes from the `LevyStochCalc.Brownian.ContinuityKolmogorovBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ContinuityDyadicChaining_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Almost-sure Hölder bounds from the Kolmogorov condition

The probabilistic half of the Kolmogorov-Chentsov construction. For a process `X` with
`∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M · edist s t ^ q`, Markov's inequality bounds each
increment tail by `M · edist s t ^ q / lam ^ p`; summing over the `2^n` level-`n` dyadic
intervals of `[0, 1]` makes the bad sets `{|increment| > ((1/2)^α)^n}` summable whenever
`α * p < q - 1`, so Borel-Cantelli gives an almost-sure bound on all small-scale dyadic
increments. Feeding those bounds to the deterministic chaining yields almost-sure local
`α`-Hölder continuity on the dyadics, and the convergence-in-measure form of the same tail
bound identifies the dyadic extension as a modification of `X`
(`kolmogorov_modification_ae_eq`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Continuity

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_14a201cfcde1fac50a3f98f3 {A : Set ℝ} (hA : Dense A) {f : ℝ → ℝ}
    {α : ℝ} (hα : 0 < α) (t : ℝ)
    (hloc : ∃ K ρ : ℝ, 0 < ρ ∧ 0 ≤ K ∧ ∀ s ∈ A, ∀ s' ∈ A,
      s ∈ Set.Ioo (t - ρ) (t + ρ) → s' ∈ Set.Ioo (t - ρ) (t + ρ) →
        |f s - f s'| ≤ K * |s - s'| ^ α) :
    ∃ y, Filter.Tendsto f (𝓝[A] t) (nhds y) := by
  obtain ⟨K, ρ, hρ, hK, hHol⟩ := hloc
  have hFne : (𝓝[A] t).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hA t)
  have hcauchy : Cauchy (Filter.map f (𝓝[A] t)) := by
    rw [Metric.cauchy_iff]
    refine ⟨hFne.map _, fun ε hε => ?_⟩
    -- choose `ρ' ≤ ρ` with `K·(2ρ')^α < ε`
    obtain ⟨ρ', hρ'0, hρ'ρ, hρ'b⟩ :
        ∃ ρ', 0 < ρ' ∧ ρ' ≤ ρ ∧ K * (2 * ρ') ^ α < ε := by
      have hδ : 0 < (ε / (K + 1)) ^ (1 / α) :=
        Real.rpow_pos_of_pos (by positivity) _
      refine ⟨min ρ ((ε / (K + 1)) ^ (1 / α) / 3), lt_min hρ (by positivity),
        min_le_left _ _, ?_⟩
      have h2 : 2 * min ρ ((ε / (K + 1)) ^ (1 / α) / 3) < (ε / (K + 1)) ^ (1 / α) := by
        have := min_le_right ρ ((ε / (K + 1)) ^ (1 / α) / 3)
        linarith
      have hpow : (2 * min ρ ((ε / (K + 1)) ^ (1 / α) / 3)) ^ α < ε / (K + 1) := by
        have h1 := Real.rpow_lt_rpow (by positivity) h2 hα
        rwa [show ((ε / (K + 1)) ^ (1 / α)) ^ α = ε / (K + 1) from by
          rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ ε / (K + 1)), one_div,
              inv_mul_cancel₀ (ne_of_gt hα), Real.rpow_one]] at h1
      calc K * (2 * min ρ ((ε / (K + 1)) ^ (1 / α) / 3)) ^ α
          ≤ (K + 1) * (2 * min ρ ((ε / (K + 1)) ^ (1 / α) / 3)) ^ α := by
            apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ < (K + 1) * (ε / (K + 1)) := by
            apply mul_lt_mul_of_pos_left hpow (by positivity)
        _ = ε := by field_simp
    refine ⟨f '' (A ∩ Set.Ioo (t - ρ') (t + ρ')), ?_, ?_⟩
    · rw [Filter.mem_map]
      refine Filter.mem_of_superset ?_ (Set.subset_preimage_image f _)
      exact inter_mem_nhdsWithin A
        (Ioo_mem_nhds (by linarith) (by linarith))
    · rintro x ⟨s, ⟨hsA, hsI⟩, rfl⟩ y ⟨s', ⟨hs'A, hs'I⟩, rfl⟩
      have hIs : s ∈ Set.Ioo (t - ρ) (t + ρ) :=
        ⟨by have := hsI.1; linarith, by have := hsI.2; linarith⟩
      have hIs' : s' ∈ Set.Ioo (t - ρ) (t + ρ) :=
        ⟨by have := hs'I.1; linarith, by have := hs'I.2; linarith⟩
      have hb := hHol s hsA s' hs'A hIs hIs'
      have hss' : |s - s'| ≤ 2 * ρ' := by
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · have h1 := hsI.1; have h2 := hs'I.2; linarith
        · have h1 := hsI.2; have h2 := hs'I.1; linarith
      rw [Real.dist_eq]
      calc |f s - f s'| ≤ K * |s - s'| ^ α := hb
        _ ≤ K * (2 * ρ') ^ α := by
            apply mul_le_mul_of_nonneg_left _ hK
            exact Real.rpow_le_rpow (abs_nonneg _) hss' hα.le
        _ < ε := hρ'b
  obtain ⟨y, hy⟩ := CompleteSpace.complete hcauchy
  exact ⟨y, hy⟩
end LevyStochCalc.Brownian.Continuity


