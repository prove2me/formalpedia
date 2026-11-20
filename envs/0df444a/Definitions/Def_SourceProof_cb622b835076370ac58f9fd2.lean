-- Prove2me | Definitions.Def_SourceProof_cb622b835076370ac58f9fd2
-- name    : SourceProof_cb622b835076370ac58f9fd2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:21:11.675469+00:00
-- url     : https://prove2.me/theorems/7b19dc57-1fc0-4669-977f-6361c61bf388
-- title:
--   LevyStochCalc source module: SourceProof_cb622b835076370ac58f9fd2
-- statement:
--   The original source theorem `ProbabilityTheory.finite_set_bound_of_edist_le` comes from the `BrownianMotion.Continuity.IsKolmogorovProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F002
import Definitions.Def_SourceProof_076e0ed6a50324520d425fcf
import Definitions.Def_SourceProof_c0c43a13c8400b1918cd8049

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

theorem _root_.Prove2MeSourceProof.h_cb622b835076370ac58f9fd2 (hJ : HasBoundedCoveringNumber J c d)
    (hJ_finite : J.Finite) (hX : IsAEKolmogorovProcess X P p q M) (hc : c ≠ ∞)
    (hd_pos : 0 < d) (hdq_lt : d < q) (hδ : δ ≠ 0) :
    ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P
      ≤ 2 ^ (2 * p + 4 * q + 1) * M * c * δ ^ (q - d)
        * (4 ^ d * (ENNReal.ofReal (Real.logb 2 (c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d))) ^ q
            + Cp d p q) := by
  by_cases hδ_le : δ / 4 ≤ Metric.ediam J
  · exact _root_.Prove2MeSourceProof.h_c0c43a13c8400b1918cd8049 hJ hJ_finite hX hc hd_pos hdq_lt hδ hδ_le
  refine (_root_.Prove2MeSourceProof.h_076e0ed6a50324520d425fcf hJ hJ_finite hX hd_pos hdq_lt ?_).trans ?_
  · exact (not_le.mp hδ_le).le
  have hX.q_pos_pos : 0 < q := hd_pos.trans hdq_lt
  calc 4 ^ p * 2 ^ q * ↑M * c * δ ^ (q - d) * ProbabilityTheory.Cp d p q
  _ ≤ 2 ^ (2 * p + 4 * q + 1) * ↑M * c * δ ^ (q - d) * ProbabilityTheory.Cp d p q := by
    gcongr
    rw [ENNReal.rpow_add _ _ (by positivity) (by simp),
      ENNReal.rpow_add _ _ (by positivity) (by simp), mul_assoc, ENNReal.rpow_one, ENNReal.rpow_mul]
    gcongr
    · exact hX.p_pos.le
    · norm_num
    calc (2 : ℝ≥0∞) ^ q
    _ ≤ 2 ^ (4 * q + 1) := by
      gcongr
      · norm_cast
      · linarith
    _ = 2 ^ (4 * q) * 2 := by
      rw [ENNReal.rpow_add _ _ (by positivity) (by simp), ENNReal.rpow_one]
  _ ≤ 2 ^ (2 * p + 4 * q + 1) * ↑M * c * δ ^ (q - d) *
      (4 ^ d * (ENNReal.ofReal (Real.logb 2 (c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d))) ^ q
      + ProbabilityTheory.Cp d p q) := by
    rw [mul_add]
    exact le_add_self
end Together

end ProbabilityTheory


