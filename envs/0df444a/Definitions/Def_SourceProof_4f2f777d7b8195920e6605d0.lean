-- Prove2me | Definitions.Def_SourceProof_4f2f777d7b8195920e6605d0
-- name    : SourceProof_4f2f777d7b8195920e6605d0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T11:02:15.770838+00:00
-- url     : https://prove2.me/theorems/519f1457-26d0-47f4-a261-9e5f938d6aa1
-- title:
--   LevyStochCalc source module: SourceProof_4f2f777d7b8195920e6605d0
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Continuity.kc_ae_nbhd_holder` comes from the `LevyStochCalc.Brownian.ContinuityKolmogorovBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ContinuityKolmogorovBounds_F001

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


theorem _root_.Prove2MeSourceProof.h_4f2f777d7b8195920e6605d0
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (hα0 : 0 < α) (hαpq : α * p < q - 1) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, ∃ K ρ : ℝ, 0 < ρ ∧ 0 ≤ K ∧ ∀ s ∈ dyadicRationals,
      ∀ s' ∈ dyadicRationals, s ∈ Set.Ioo (t - ρ) (t + ρ) →
        s' ∈ Set.Ioo (t - ρ) (t + ρ) → |X s ω - X s' ω| ≤ K * |s - s'| ^ α := by
  filter_upwards [LevyStochCalc.Brownian.Continuity.kc_ae_interval_holder P X hX hα0 hαpq] with ω hIH
  intro t
  set c : ℤ := ⌊t + 1 / 2⌋ with hc
  obtain ⟨KL, NL, hKL0, hHL⟩ := hIH (c - 1)
  obtain ⟨K₀, N₀, hK₀0, hH₀⟩ := hIH c
  have hcdy : (c : ℝ) ∈ LevyStochCalc.Brownian.Continuity.dyadicRationals := LevyStochCalc.Brownian.Continuity.intCast_mem_dyadicRationals c
  -- `t` lies within `1/2` of `c`.
  have htlo : (c : ℝ) - 1 / 2 ≤ t := by
    have := Int.floor_le (t + 1 / 2); linarith
  have hthi : t < (c : ℝ) + 1 / 2 := by
    have := Int.lt_floor_add_one (t + 1 / 2); linarith
  refine ⟨2 * (KL + K₀),
    min (min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀) / 2) (1 / 2), ?_, by positivity, ?_⟩
  · have : (0 : ℝ) < min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀) := by positivity
    exact lt_min (by positivity) (by norm_num)
  · set ρ := min (min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀) / 2) (1 / 2) with hρ
    have hρ12 : ρ ≤ 1 / 2 := min_le_right _ _
    have hrhoNL : 2 * ρ ≤ (1 / 2 : ℝ) ^ NL := by
      have h1 : ρ ≤ min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀) / 2 := min_le_left _ _
      have h2 : min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀)
          ≤ (1 / 2 : ℝ) ^ NL := min_le_left _ _
      linarith
    have hρN₀ : 2 * ρ ≤ (1 / 2 : ℝ) ^ N₀ := by
      have h1 : ρ ≤ min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀) / 2 := min_le_left _ _
      have h2 : min ((1 / 2 : ℝ) ^ NL) ((1 / 2 : ℝ) ^ N₀)
          ≤ (1 / 2 : ℝ) ^ N₀ := min_le_right _ _
      linarith
    -- ordered-pair core
    have key : ∀ a b, a ∈ LevyStochCalc.Brownian.Continuity.dyadicRationals → b ∈ LevyStochCalc.Brownian.Continuity.dyadicRationals →
        (c : ℝ) - 1 < a → a ≤ b → b < (c : ℝ) + 1 → |a - b| ≤ 2 * ρ →
        |X a ω - X b ω| ≤ 2 * (KL + K₀) * |a - b| ^ α := by
      intro a b ha hb halo hab bhi habs
      have habsL : |a - b| ≤ (1 / 2 : ℝ) ^ NL := le_trans habs hrhoNL
      have habs₀ : |a - b| ≤ (1 / 2 : ℝ) ^ N₀ := le_trans habs hρN₀
      rcases le_or_gt b (c : ℝ) with hbc | hbc
      · -- both in [c-1, c]
        have h := hHL a ha b hb (by push_cast; linarith) (by push_cast; linarith)
          (by push_cast; linarith) (by push_cast; linarith) habsL
        have : KL ≤ 2 * (KL + K₀) := by nlinarith
        calc |X a ω - X b ω| ≤ KL * |a - b| ^ α := h
          _ ≤ 2 * (KL + K₀) * |a - b| ^ α := by
              apply mul_le_mul_of_nonneg_right this (by positivity)
      · rcases le_or_gt (c : ℝ) a with hca | hca
        · -- both in [c, c+1]
          have h := hH₀ a ha b hb (by linarith) (by linarith)
            (by linarith) (by linarith) habs₀
          have : K₀ ≤ 2 * (KL + K₀) := by nlinarith
          calc |X a ω - X b ω| ≤ K₀ * |a - b| ^ α := h
            _ ≤ 2 * (KL + K₀) * |a - b| ^ α := by
                apply mul_le_mul_of_nonneg_right this (by positivity)
        · -- straddle: a < c < b, chain through c
          have hac_le : |a - (c : ℝ)| ≤ |a - b| := by
            rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
          have hcb_le : |(c : ℝ) - b| ≤ |a - b| := by
            rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
          have h1 := hHL a ha (c : ℝ) hcdy (by push_cast; linarith) (by push_cast; linarith)
            (by push_cast; linarith) (by push_cast; linarith) (le_trans hac_le habsL)
          have h2 := hH₀ (c : ℝ) hcdy b hb (by linarith) (by linarith)
            (by linarith) (by linarith) (le_trans hcb_le habs₀)
          have hacα : |a - (c : ℝ)| ^ α ≤ |a - b| ^ α :=
            Real.rpow_le_rpow (abs_nonneg _) hac_le hα0.le
          have hcbα : |(c : ℝ) - b| ^ α ≤ |a - b| ^ α :=
            Real.rpow_le_rpow (abs_nonneg _) hcb_le hα0.le
          calc |X a ω - X b ω|
              ≤ |X a ω - X (c : ℝ) ω| + |X (c : ℝ) ω - X b ω| := abs_sub_le _ _ _
            _ ≤ KL * |a - (c : ℝ)| ^ α + K₀ * |(c : ℝ) - b| ^ α := by gcongr
            _ ≤ KL * |a - b| ^ α + K₀ * |a - b| ^ α := by gcongr
            _ ≤ 2 * (KL + K₀) * |a - b| ^ α := by
                nlinarith [Real.rpow_nonneg (abs_nonneg (a - b)) α]
    intro s hs s' hs' hsb hs'b
    have hsbnd : (c : ℝ) - 1 < s ∧ s < (c : ℝ) + 1 :=
      ⟨by have := hsb.1; linarith, by have := hsb.2; linarith⟩
    have hs'bnd : (c : ℝ) - 1 < s' ∧ s' < (c : ℝ) + 1 :=
      ⟨by have := hs'b.1; linarith, by have := hs'b.2; linarith⟩
    have hdist : |s - s'| ≤ 2 * ρ := by
      rw [abs_le]; constructor
      · have := hsb.1; have := hs'b.2; linarith
      · have := hsb.2; have := hs'b.1; linarith
    rcases le_total s s' with hss | hss
    · exact key s s' hs hs' hsbnd.1 hss hs'bnd.2 hdist
    · rw [abs_sub_comm, abs_sub_comm s s']
      exact key s' s hs' hs hs'bnd.1 hss hsbnd.2 (by rw [abs_sub_comm] at hdist; exact hdist)
end LevyStochCalc.Brownian.Continuity


