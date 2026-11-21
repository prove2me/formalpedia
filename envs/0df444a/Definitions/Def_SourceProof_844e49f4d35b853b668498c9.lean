-- Prove2me | Definitions.Def_SourceProof_844e49f4d35b853b668498c9
-- name    : SourceProof_844e49f4d35b853b668498c9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:07:13.676092+00:00
-- url     : https://prove2.me/theorems/e66a8a75-f499-47ab-a252-db89c4305383
-- title:
--   LevyStochCalc source module: SourceProof_844e49f4d35b853b668498c9
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.stageLp_cauchySeq` comes from the `LevyStochCalc.Poisson.CompensatedProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatedProcess_F000
import Definitions.Def_SourceProof_6ac2e280d1dcf21fddfd48d3

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated-Poisson `L²` integral process

The process `t ↦ ∫_0^t ∫_E φ(s, e) Ñ(ds, de)` is the `L²`-limit, at each time `t`, of the
compensated integrals of the master approximating sequence (`stageIntegral`). It is taken as
the `ℱ_t`-measurable representative of the `L²`-limit, so that it is adapted to the natural
filtration of the Poisson random measure; it is a square-integrable martingale, vanishes at
nonpositive times, and satisfies the Itô–Lévy isometry at every time.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

section Process

include hℱ in

theorem _root_.Prove2MeSourceProof.h_844e49f4d35b853b668498c9 (t : ℝ) :
    CauchySeq (fun n => stageLp N ℱ φ h_meas h_progMeas h_sq_int_global t n) := by
  rw [EMetric.cauchySeq_iff]
  intro ε hε
  by_cases hε_top : ε = ⊤
  · exact ⟨0, fun m _ n _ => by rw [hε_top]; exact lt_top_iff_ne_top.mpr (edist_ne_top _ _)⟩
  have hε2 : ε ^ (2 : ℝ) / 4 ≠ 0 :=
    (ENNReal.div_pos (ENNReal.rpow_pos hε hε_top).ne' (by norm_num)).ne'
  obtain ⟨N₁, hN₁⟩ := ENNReal.exists_inv_nat_lt hε2
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, t ≤ LevyStochCalc.Poisson.Compensated.stageHorizon N₀ := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt t (one_lt_two : (1 : ℝ) < 2)
    exact ⟨k, hk.le⟩
  refine ⟨max N₀ N₁, fun m hm n hn => ?_⟩
  rw [LevyStochCalc.Poisson.Compensated.stageLp, LevyStochCalc.Poisson.Compensated.stageLp, Lp.edist_toLp_toLp]
  have hbound : ∀ {a b : ℕ}, a ≤ b → max N₀ N₁ ≤ a →
      ∫⁻ ω, (‖LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global a t ω
        - LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global b t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        < ε ^ (2 : ℝ) := by
    intro a b hab ha
    have hta : t ≤ LevyStochCalc.Poisson.Compensated.stageHorizon a := hN₀.trans (LevyStochCalc.Poisson.Compensated.stageHorizon_mono ((le_max_left _ _).trans ha))
    refine lt_of_le_of_lt (_root_.Prove2MeSourceProof.h_6ac2e280d1dcf21fddfd48d3 N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hab
      hta)
      ?_
    have hinv : ∀ {c : ℕ}, N₁ ≤ c → ((c : ℝ≥0∞) + 1)⁻¹ < ε ^ (2 : ℝ) / 4 := fun {c} hc =>
      lt_of_le_of_lt (ENNReal.inv_le_inv.2 (le_trans (by exact_mod_cast hc) le_self_add)) hN₁
    have h1 := hinv ((le_max_right N₀ N₁).trans ha)
    have h2 := hinv ((le_max_right N₀ N₁).trans (ha.trans hab))
    calc 2 * ((a : ℝ≥0∞) + 1)⁻¹ + 2 * ((b : ℝ≥0∞) + 1)⁻¹
        = ((a : ℝ≥0∞) + 1)⁻¹ * 2 + ((b : ℝ≥0∞) + 1)⁻¹ * 2 := by ring
      _ < ε ^ (2 : ℝ) / 4 * 2 + ε ^ (2 : ℝ) / 4 * 2 :=
          ENNReal.add_lt_add (ENNReal.mul_lt_mul_left (by norm_num) (by norm_num) h1)
            (ENNReal.mul_lt_mul_left (by norm_num) (by norm_num) h2)
      _ = ε ^ (2 : ℝ) := by
          rw [show ε ^ (2 : ℝ) / 4 * 2 + ε ^ (2 : ℝ) / 4 * 2 = 4 * (ε ^ (2 : ℝ) / 4) by ring,
            ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
  have hsq : eLpNorm (fun ω => LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global m t ω
      - LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω) 2 P ^ (2 : ℝ)
      < ε ^ (2 : ℝ) := by
    rw [LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq]
    rcases le_total m n with hmn | hnm
    · exact hbound hmn hm
    · have := hbound hnm hn
      refine lt_of_eq_of_lt (lintegral_congr fun ω => ?_) this
      rw [← nnnorm_neg, neg_sub]
  have h := (ENNReal.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp hsq
  refine lt_of_eq_of_lt ?_ h
  rfl
end Process

section Isometry

end Isometry

end LevyStochCalc.Poisson.Compensated


