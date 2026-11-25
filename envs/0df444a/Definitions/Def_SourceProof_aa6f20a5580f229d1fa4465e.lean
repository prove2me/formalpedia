-- Prove2me | Definitions.Def_SourceProof_aa6f20a5580f229d1fa4465e
-- name    : SourceProof_aa6f20a5580f229d1fa4465e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:58.56994+00:00
-- url     : https://prove2.me/theorems/f697e8b1-5dd3-4d5c-a95a-52c19bf0b490
-- title:
--   StochLean source theorem: ProbabilityTheory.IsConditionalIncrementModulus.ae_le_of_norm_bound

import Definitions.Def_SourceProof_a54f17b20359f1a9dacf5570

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Version-safe conditional increment moduli

The compact short-window modulus is specified as a measurable essential supremum,
not as the pointwise supremum of arbitrarily chosen uncountably many conditional
expectations. Existence and almost-sure uniqueness precede any representative choice.
The diagonal is included, so taking positive parts does not change a consistent
supremum. These interfaces do not yet assert small-window convergence.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable {F : Filtration ℝ≥0 mΩ} {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
  {T δ η : ℝ≥0} {W V : Ω → ℝ≥0∞}

namespace IsConditionalIncrementModulus
theorem _root_.Prove2MeSourceProof.h_aa6f20a5580f229d1fa4465e [IsFiniteMeasure P]
    (hW : IsConditionalIncrementModulus F P X T δ W) {N : ℝ}
    (hi : ∀ t, t ≤ T → Integrable (X t) P)
    (hb : ∀ t, t ≤ T → ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N) :
    W ≤ᵐ[P] (fun _ ↦ ENNReal.ofReal (2 * N)) := by
  apply (_root_.Prove2MeSourceProof.h_a54f17b20359f1a9dacf5570 hW)
  intro t u htu huT _
  have htuT := htu.trans huT
  have hdiff : X t - X u ≤ᵐ[P] (fun _ ↦ 2 * N) := by
    filter_upwards [hb t htuT, hb u huT] with ω ht hu
    have hnorm := (norm_sub_le (X t ω) (X u ω)).trans (add_le_add ht hu)
    have hs : X t ω - X u ω ≤ ‖X t ω - X u ω‖ := by
      simpa only [Real.norm_eq_abs] using le_abs_self (X t ω - X u ω)
    change X t ω - X u ω ≤ 2 * N
    linarith
  have hce := condExp_mono (m := F t) ((hi t htuT).sub (hi u huT))
    (integrable_const (2 * N)) hdiff
  rw [condExp_const (F.le t)] at hce
  exact hce.mono fun _ hω ↦ ENNReal.ofReal_le_ofReal hω
end IsConditionalIncrementModulus

end ProbabilityTheory


