-- Prove2me | Definitions.Def_SourceProof_6374558db2ae582746501262
-- name    : SourceProof_6374558db2ae582746501262
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:28:12.610801+00:00
-- url     : https://prove2.me/theorems/dd7bc66c-07c0-4dde-96e5-ea0085550442
-- title:
--   StochLean source theorem: ProbabilityTheory.eVariationOn_univ_indicator_lifetime_le

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Probability_Process_FiniteVariation_SingleJump_F000

open private eVariationOn_step_Ici_univ from Definitions.Def_StochLean_Probability_Process_FiniteVariation_SingleJump_F000
/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual integrable variation of a single lifetime step

The closed-step process uses the existing lifetime indicator. Its whole-half-line
extended variation is exactly the norm of its coefficient at a positive finite
lifetime, and zero at zero or infinite lifetime. A zero lifetime gives a constant
path, so its initial value contributes no variation. An infinite lifetime never
activates at a finite time.

The variation formula is pathwise and needs no measurability. A measurable
lifetime and an integrable coefficient then give actual integrable variation
and its expectation bound. Neither a filtration, a stopping-time hypothesis,
finiteness of the measure, nor a zero initial value is required. Finiteness of
the extended variation is proved before using its real conversion.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {τ : Ω → WithTop ℝ≥0} {Z : Ω → ℝ}


theorem _root_.Prove2MeSourceProof.h_6374558db2ae582746501262 (τ : Ω → WithTop ℝ≥0)
    (Z : Ω → ℝ) (ω : Ω) :
    eVariationOn
      (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z ω) univ =
        if 0 < τ ω ∧ τ ω < ⊤ then ENNReal.ofReal ‖Z ω‖ else 0 := by
  classical
  cases ht : τ ω with
  | top =>
    simp only [indicator_apply, mem_ofPred_eq, ht, WithTop.not_top_le_coe,
      if_false, lt_self_iff_false, and_false]
    exact (eVariationOn.eq_zero_iff _).mpr fun _ _ _ _ ↦ edist_self 0
  | coe a =>
    simpa only [indicator_apply, mem_ofPred_eq, ht, WithTop.coe_le_coe,
      WithTop.coe_lt_top, and_true, ← WithTop.coe_zero, WithTop.coe_lt_coe] using
        eVariationOn_step_Ici_univ a (Z ω)
end ProbabilityTheory


