-- Prove2me | Definitions.Def_SourceProof_c0c43a13c8400b1918cd8049
-- name    : SourceProof_c0c43a13c8400b1918cd8049
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:12:47.345636+00:00
-- url     : https://prove2.me/theorems/0151346a-987a-48e3-82a8-c68e8dd7ec6c
-- title:
--   LevyStochCalc source module: SourceProof_c0c43a13c8400b1918cd8049
-- statement:
--   The original source theorem `ProbabilityTheory.finite_set_bound_of_edist_le_of_le_diam'` comes from the `BrownianMotion.Continuity.IsKolmogorovProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_60ef4b5b5ba17082ee1e5b8b

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Stochastic processes satisfying the Kolmogorov condition

-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal Finset

section Aux

end Aux

namespace ProbabilityTheory

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E]
  {p q : ℝ} {M : ℝ≥0} {P : Measure Ω} {X : T → Ω → E}

section Measurability

variable [MeasurableSpace E] [BorelSpace E]

end Measurability

section FirstTerm

variable {J : Set T}

end FirstTerm

section SecondTerm

variable {J : Set T} {C : ℕ → Finset T} {ε : ℕ → ℝ≥0} {j k m : ℕ}

end SecondTerm

section Together

variable {M : ℝ≥0} {d p q : ℝ} {J : Set T} {c : ℝ≥0∞} {δ : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_c0c43a13c8400b1918cd8049 (hJ : HasBoundedCoveringNumber J c d)
    (hJ_finite : J.Finite) (hX : IsAEKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q)
    (hδ : δ ≠ 0) (hδ_le : δ / 4 ≤ Metric.ediam J) :
    ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P
      ≤ 2 ^ (2 * p + 4 * q + 1) * M * c * δ ^ (q - d)
        * (4 ^ d * (ENNReal.ofReal (Real.logb 2 (c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d))) ^ q
            + Cp d p q) := by
  have h_diam_lt_top : Metric.ediam J < ∞ := hJ.ediam_lt_top
  refine (_root_.Prove2MeSourceProof.h_60ef4b5b5ba17082ee1e5b8b hJ hJ_finite hX hd_pos hdq_lt hδ
    hδ_le).trans ?_
  simp_rw [mul_assoc]
  gcongr _ * (_ * ?_)
  simp_rw [mul_add, ← mul_assoc]
  gcongr ?_ + ?_
  · rw [mul_comm c]
    simp_rw [mul_assoc]
    gcongr _ * ?_
    simp_rw [← mul_assoc]
    have hδ_ne_top : δ ≠ ∞ := by
      refine ne_of_lt ?_
      calc (δ : ℝ≥0∞)
      _ ≤ 4 * Metric.ediam J := by rwa [ENNReal.div_le_iff' (by simp) (by simp)] at hδ_le
      _ < ∞ := ENNReal.mul_lt_top (by simp) h_diam_lt_top
    have hJδ := hJ.coveringNumber_le (δ / 4) (by simpa)
    have hJ' : coveringNumber (δ / 4) J ≤ c * 4 ^ d * δ⁻¹ ^ d := by
      refine hJδ.trans_eq ?_
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_div, ENNReal.coe_ofNat]
      rw [ENNReal.inv_div, ENNReal.div_rpow_of_nonneg, div_eq_mul_inv, ENNReal.coe_inv hδ,
        ENNReal.inv_rpow]
      · ring
      · exact hd_pos.le
      · simp
      · exact .inr <| mod_cast hδ
    have hJ'' : Nat.log2 (coveringNumber (δ / 4) J).toNat
        ≤ ENNReal.ofReal (Real.logb 2 (c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d)) := by
      by_cases h0 : Nat.log2 (coveringNumber (δ / 4) J).toNat = 0
      · simp [h0]
      refine (ENNReal.natCast_le_ofReal h0).mpr ?_
      calc (Nat.log2 (coveringNumber (δ / 4) J).toNat : ℝ)
      _ ≤ Real.logb 2 (coveringNumber (δ / 4) J).toNat := Real.log2_le_logb _
      _ ≤ Real.logb 2 (c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d) := by
        have h_ne_top : coveringNumber (δ / 4) J ≠ ⊤ := by
          refine (hJ.coveringNumber_lt_top ?_ hc hd_pos.le).ne
          simp [hδ]
        gcongr
        · simp
        · by_contra h_eq
          simp only [Nat.cast_pos, not_lt, nonpos_iff_eq_zero, ENat.toNat_eq_zero, h_ne_top,
            or_false] at h_eq
          simp [h_eq] at h0
        have h_toReal : c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d
            = (c * 4 ^ d * δ⁻¹ ^ d).toReal := by simp [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
        rw [h_toReal, ← ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg, ENNReal.ofReal_toReal]
        · refine le_trans (le_of_eq ?_) hJ'
          norm_cast
          simp [h_ne_top]
        · finiteness
    have hX.q_pos_pos : 0 < q := hd_pos.trans hdq_lt
    calc (δ : ℝ≥0∞) ^ d * (Nat.log2 (coveringNumber (δ / 4) J).toNat) ^ q
        * (coveringNumber (δ / 4) J)
    _ ≤ δ ^ d * (ENNReal.ofReal (Real.logb 2 (c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d))) ^ q
        * (c * 4 ^ d * δ⁻¹ ^ d) := by gcongr
    _ = c * 4 ^ d * (ENNReal.ofReal (Real.logb 2 (c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d))) ^ q := by
      rw [ENNReal.coe_inv hδ, ENNReal.inv_rpow]
      simp_rw [mul_assoc]
      rw [mul_comm]
      simp_rw [← mul_assoc, mul_assoc]
      rw [ENNReal.inv_mul_cancel]
      · ring
      · simp [hδ]
      · simp [hδ_ne_top, hδ]
  · exact le_of_eq (by ring)
end Together

end ProbabilityTheory


