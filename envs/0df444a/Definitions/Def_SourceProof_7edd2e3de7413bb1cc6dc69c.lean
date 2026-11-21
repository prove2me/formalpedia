-- Prove2me | Definitions.Def_SourceProof_7edd2e3de7413bb1cc6dc69c
-- name    : SourceProof_7edd2e3de7413bb1cc6dc69c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:10:54.701534+00:00
-- url     : https://prove2.me/theorems/438ec3c5-a94c-4496-8924-27464882af93
-- title:
--   LevyStochCalc source module: SourceProof_7edd2e3de7413bb1cc6dc69c
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.masterLp_cauchySeq` comes from the `LevyStochCalc.Brownian.ItoL2CompletionMaster` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F001
import Definitions.Def_SourceProof_41ed6a895f066f4ae221ca65
import Definitions.Def_SourceProof_f68e93dfb81b09358de9c4e9

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the master approximating sequence

The master sequence `masterApprox` of adapted simple predictable integrands on the
growing horizons `[0, n + 1]`, its Cauchy property in `L²(P)` uniformly on compact
time intervals, the limit `masterLp` and `stochasticIntegralBrownianLp` in
`Lp ℝ 2 P`, and the process `stochasticIntegralBrownian` together with its
adaptedness, vanishing on negative times and `ℱ`-martingale property.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section MasterSequence

variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_7edd2e3de7413bb1cc6dc69c {t : ℝ} (ht_nn : 0 ≤ t) :
    CauchySeq (fun n => masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n) := by
  rw [EMetric.cauchySeq_iff]
  intro ε hε
  by_cases hε_top : ε = ⊤
  · refine ⟨⌈t⌉₊, fun m hm n hn => ?_⟩
    rw [hε_top]; exact lt_top_iff_ne_top.mpr (edist_ne_top _ _)
  · set δ : ℝ≥0∞ := ε ^ (2 : ℝ) / 4 with hδ
    have hε2_ne_top : ε ^ (2 : ℝ) ≠ ⊤ := by
      simp [hε_top]
    have hδ_pos : 0 < δ := by
      rw [hδ]; exact ENNReal.div_pos (ENNReal.rpow_pos hε hε_top).ne' (by norm_num)
    have htend := _root_.Prove2MeSourceProof.h_f68e93dfb81b09358de9c4e9 (t := t) ℱ H h_meas h_progMeas h_sq_int_global
    have hev : ∀ᶠ k in Filter.atTop,
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖H ω s - (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global k).eval s ω‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P < δ := htend (Iio_mem_nhds hδ_pos)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N0, hN0⟩ := hev
    refine ⟨max N0 ⌈t⌉₊, fun m hm n hn => ?_⟩
    have hmt : t ≤ (m : ℝ) + 1 := by
      have : (⌈t⌉₊ : ℝ) ≤ (m : ℝ) := by exact_mod_cast (le_max_right N0 ⌈t⌉₊).trans hm
      have := Nat.le_ceil t; linarith
    have hnt : t ≤ (n : ℝ) + 1 := by
      have : (⌈t⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_max_right N0 ⌈t⌉₊).trans hn
      have := Nat.le_ceil t; linarith
    have hmN0 : N0 ≤ m := (le_max_left N0 ⌈t⌉₊).trans hm
    have hnN0 : N0 ≤ n := (le_max_left N0 ⌈t⌉₊).trans hn
    -- edist = eLpNorm of the integral difference
    have em : LevyStochCalc.Brownian.Ito.masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t m
        = (_root_.Prove2MeSourceProof.h_f748d28952e895ba511897bd W ℱ hℱ (LevyStochCalc.Brownian.Ito.master_horizon_pos m)
            (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global m)
            (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global m) ht_nn hmt).toLp := by
      rw [LevyStochCalc.Brownian.Ito.masterLp]; exact dif_pos ⟨ht_nn, hmt⟩
    have en : LevyStochCalc.Brownian.Ito.masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n
        = (_root_.Prove2MeSourceProof.h_f748d28952e895ba511897bd W ℱ hℱ (LevyStochCalc.Brownian.Ito.master_horizon_pos n)
            (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
            (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n) ht_nn hnt).toLp := by
      rw [LevyStochCalc.Brownian.Ito.masterLp]; exact dif_pos ⟨ht_nn, hnt⟩
    have h_edist : edist (LevyStochCalc.Brownian.Ito.masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t m)
          (LevyStochCalc.Brownian.Ito.masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n)
        = MeasureTheory.eLpNorm
            (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global m) t ω
              - LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
                h_sq_int_global n) t ω) 2 P := by
      rw [em, en]
      exact MeasureTheory.Lp.edist_toLp_toLp _ _ _ _
    rw [h_edist]
    -- eLpNorm² < ε²  ⇒  eLpNorm < ε
    have h_sq_lt : MeasureTheory.eLpNorm
        (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global m) t ω
          - LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t ω) 2 P
          ^ (2 : ℝ) < ε ^ (2 : ℝ) := by
      rw [LevyStochCalc.Brownian.Ito.eLpNorm_two_rpow_eq_lintegral_sq]
      refine lt_of_le_of_lt
        (_root_.Prove2MeSourceProof.h_41ed6a895f066f4ae221ca65 W ℱ hℱ H h_meas h_progMeas h_sq_int_global m n ht_nn) ?_
      have hsum : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H ω s - (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global m).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H ω s - (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P < δ + δ :=
        ENNReal.add_lt_add (hN0 m hmN0) (hN0 n hnN0)
      calc 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
                (‖H ω s - (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
                  h_sq_int_global m).eval s ω‖₊ : ℝ≥0∞) ^ 2
                  ∂volume ∂P)
              + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
                (‖H ω s - (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
                  h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
                  ∂volume ∂P)
          < 2 * (δ + δ) := by gcongr; first | exact hsum | simp
        _ = ε ^ (2 : ℝ) := by
            have h4 : (2 : ℝ≥0∞) * (δ + δ) = 4 * δ := by ring
            rw [h4, hδ, ENNReal.mul_div_cancel (show (4 : ℝ≥0∞) ≠ 0 by norm_num)
              (show (4 : ℝ≥0∞) ≠ ⊤ by simp)]
    exact (ENNReal.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp h_sq_lt
end MasterSequence

end LevyStochCalc.Brownian.Ito


