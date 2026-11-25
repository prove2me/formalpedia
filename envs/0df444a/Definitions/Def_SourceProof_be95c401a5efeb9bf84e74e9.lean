-- Prove2me | Definitions.Def_SourceProof_be95c401a5efeb9bf84e74e9
-- name    : SourceProof_be95c401a5efeb9bf84e74e9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:46:26.471575+00:00
-- url     : https://prove2.me/theorems/a57c4d86-b947-4dc9-9d65-9566f5110b6a
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.secondDifferenceWeight_ne_zero_on_identificationSet

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F010
import Definitions.Def_SourceProof_aa8efee0d1e9dbf694c57465

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Lévy triplets and the fixed truncation convention

This module fixes the data and truncation convention used by the real Lévy--Khintchine layer.  It
does not store an infinitely-divisible law or a representation theorem inside the triplet.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

namespace LevyTriplet

theorem _root_.Prove2MeSourceProof.h_be95c401a5efeb9bf84e74e9 (n : ℕ)
    {x : ℝ} (hx : x ∈ levyIdentificationSet n) :
    secondDifferenceWeight ((n + 1 : ℝ)⁻¹) x ≠ 0 := by
  have hden : 0 < (n + 1 : ℝ) := by positivity
  have hxabs : |x / (n + 1 : ℝ)| < 2 * Real.pi := by
    rw [abs_div, abs_of_pos hden, div_lt_iff₀ hden]
    simpa only [ProbabilityTheory.LevyTriplet.levyIdentificationSet, Set.mem_setOf_eq, mul_assoc] using hx.2
  have hybounds := (abs_lt.mp hxabs)
  have harg : (n + 1 : ℝ)⁻¹ * x = x / (n + 1 : ℝ) := by
    field_simp
  have hcos : Real.cos ((n + 1 : ℝ)⁻¹ * x) ≠ 1 := by
    intro hc
    rw [harg] at hc
    have hz := (Real.cos_eq_one_iff_of_lt_of_lt hybounds.1 hybounds.2).mp hc
    have : x = 0 := by
      apply (div_eq_zero_iff).mp hz |>.resolve_right
      positivity
    exact (abs_pos.mp hx.1) this
  intro hw
  have hw' := congrArg (fun r : ℝ≥0 => (r : ℝ)) hw
  rw [_root_.Prove2MeSourceProof.h_aa8efee0d1e9dbf694c57465] at hw'
  norm_num at hw'
  apply hcos
  nlinarith
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


