-- Prove2me | Definitions.Def_SourceProof_757df108f391058e4c34f0a1
-- name    : SourceProof_757df108f391058e4c34f0a1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:31:36.654922+00:00
-- url     : https://prove2.me/theorems/2e3b29f5-96f8-4f91-aacd-13b70671c36f
-- title:
--   StochLean source theorem: ProbabilityTheory.eVariationOn_univ_tsum_indicator_lifetime_le

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Probability_Process_Path_LifetimeStepSeries_F000
import Definitions.Def_SourceProof_ae1716f004858c52c8ec1d3b

open private eVariationOn_finset_indicator_lifetime_le from Definitions.Def_StochLean_Probability_Process_Path_LifetimeStepSeries_F000
/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Absolutely summable steps at finite or infinite lifetimes

The actual sum of closed lifetime steps converges uniformly on the entire
half-line, has cadlag paths, and has whole-half-line variation bounded by the
sum of the coefficient norms. Lifetimes may coincide, be zero, or be infinite.
No arbitrary finite replacement of an infinite lifetime is used: its step is
zero at every finite time. The sum is the ordinary existing `tsum` expression,
and its convergence is proved from absolute summability.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable (τ : ℕ → WithTop ℝ≥0) {K : ℕ → ℝ}


theorem _root_.Prove2MeSourceProof.h_757df108f391058e4c34f0a1
    (hK : Summable (fun n ↦ ‖K n‖)) :
    eVariationOn
      (fun t : ℝ≥0 ↦ ∑' n, if τ n ≤ (t : WithTop ℝ≥0) then K n else 0) univ ≤
        ENNReal.ofReal (∑' n, ‖K n‖) := by
  have hu := _root_.Prove2MeSourceProof.h_ae1716f004858c52c8ec1d3b τ hK
  have hb (N : ℕ) :
      eVariationOn
        (fun t : ℝ≥0 ↦ ∑ n ∈ Finset.range N,
          if τ n ≤ (t : WithTop ℝ≥0) then K n else 0) univ ≤
            ENNReal.ofReal (∑' n, ‖K n‖) :=
    (eVariationOn_finset_indicator_lifetime_le τ (Finset.range N)).trans
      (ENNReal.ofReal_le_ofReal (hK.sum_le_tsum _ (fun _ _ ↦ norm_nonneg _)))
  apply le_of_forall_lt_imp_le_of_dense
  intro c hc
  have he := eVariationOn.lowerSemicontinuous_aux
    (fun t (_ : t ∈ (univ : Set ℝ≥0)) ↦ hu.tendsto_at t) hc
  obtain ⟨N, hN⟩ := he.exists
  exact hN.le.trans (hb N)
end ProbabilityTheory


