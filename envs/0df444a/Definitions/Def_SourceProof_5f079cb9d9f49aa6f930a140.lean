-- Prove2me | Definitions.Def_SourceProof_5f079cb9d9f49aa6f930a140
-- name    : SourceProof_5f079cb9d9f49aa6f930a140
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:48:51.188596+00:00
-- url     : https://prove2.me/theorems/197b7669-3ff1-4f01-9d00-d68567bbe1b3
-- title:
--   LevyStochCalc source module: SourceProof_5f079cb9d9f49aa6f930a140
-- statement:
--   The original source theorem `HasBoundedCoveringNumber.subset` comes from the `BrownianMotion.Continuity.HasBoundedInternalCoveringNumber` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_HasBoundedInternalCoveringNumber_F000

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# HasBoundedCoveringNumber

-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal

variable {T : Type*} [PseudoEMetricSpace T] {A : Set T} {c : ℝ≥0∞} {ε : ℝ≥0} {d : ℝ}

theorem _root_.Prove2MeSourceProof.h_5f079cb9d9f49aa6f930a140 {B : Set T}
    (h : HasBoundedCoveringNumber A c d) (hBA : B ⊆ A) (hd : 0 ≤ d) :
    HasBoundedCoveringNumber B (2 ^ d * c) d := by
  constructor
  · exact lt_of_le_of_lt (Metric.ediam_mono hBA) h.ediam_lt_top
  intro ε hε_le
  by_cases hdA : d = 0 ∧ Metric.ediam A = ∞
  · simp only [hdA.1, ENNReal.rpow_zero, one_mul, mul_one]
    replace h := h.coveringNumber_le 0 (by simp)
    simp only [hdA.1, ENNReal.rpow_zero, mul_one] at h
    calc (coveringNumber ε B : ℝ≥0∞)
    _ ≤ coveringNumber 0 B := mod_cast coveringNumber_anti zero_le
    _ ≤ coveringNumber (0 / 2) A := mod_cast coveringNumber_subset_le hBA
    _ = coveringNumber 0 A := by simp
    _ ≤ c := h
  push Not at hdA
  calc (coveringNumber ε B : ℝ≥0∞)
  _ ≤ coveringNumber (ε / 2) A := mod_cast coveringNumber_subset_le hBA
  _ ≤ c * (ε / 2 : ℝ≥0∞)⁻¹ ^ d := by
    replace h := h.coveringNumber_le (ε / 2) ?_
    · simpa using h
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_div, ENNReal.coe_ofNat]
      calc (ε / 2 : ℝ≥0∞) ≤ ε := ENNReal.half_le_self
      _ ≤ Metric.ediam B := hε_le
      _ ≤ Metric.ediam A := Metric.ediam_mono hBA
  _ = 2 ^ d * c * (ε : ℝ≥0∞)⁻¹ ^ d := by
    rw [div_eq_mul_inv, ENNReal.mul_inv (by simp) (by simp), inv_inv,
      ENNReal.mul_rpow_of_nonneg _ _ hd]
    ring


