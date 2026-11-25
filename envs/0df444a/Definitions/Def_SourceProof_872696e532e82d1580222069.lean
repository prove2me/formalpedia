-- Prove2me | Definitions.Def_SourceProof_872696e532e82d1580222069
-- name    : SourceProof_872696e532e82d1580222069
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:31:27.143772+00:00
-- url     : https://prove2.me/theorems/dad59596-1ce7-4d9b-863a-33bcee80f715
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.integral_sq_eq_integral_predictableQuadraticVariation

import Definitions.Def_StochLean_Probability_Martingale_QuadraticVariation_F001
import Definitions.Def_SourceProof_748bfdc79db837cfeb806edd
import Definitions.Def_SourceProof_ce98c22b423cb6d74f7bb08a
import Definitions.Def_SourceProof_dff4282bdbe72b40f691dd9d

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Quadratic variation and predictable bracket in discrete time

The pathwise quadratic variation `[M]` and the predictable bracket `⟨M⟩` are deliberately
different definitions.  The latter is the Doob predictable part (compensator) of the former.
-/

@[expose] public section

open scoped BigOperators ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace Martingale

theorem _root_.Prove2MeSourceProof.h_872696e532e82d1580222069
    {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝓕]
    (hM : Martingale M 𝓕 μ) (hM_two : ∀ n, MemLp (M n) 2 μ)
    (hM_zero : M 0 = 0) (n : ℕ) :
    ∫ ω, (M n ω) ^ 2 ∂μ =
      ∫ ω, predictableQuadraticVariation M 𝓕 μ n ω ∂μ := by
  have hmart := (_root_.Prove2MeSourceProof.h_748bfdc79db837cfeb806edd hM) hM_two
  have hzero := hmart.setIntegral_eq (Nat.zero_le n) (s := Set.univ) MeasurableSet.univ
  have hΔ : ∀ k, Integrable ((M (k + 1) - M k) ^ 2) μ :=
    fun k => ((hM_two (k + 1)).sub (hM_two k)).integrable_sq
  simp only [Measure.restrict_univ,
    _root_.Prove2MeSourceProof.h_ce98c22b423cb6d74f7bb08a, sub_zero] at hzero
  rw [hM_zero] at hzero
  change (∫ _ω, (0 : ℝ) ^ 2 ∂μ) =
    ∫ ω, M n ω ^ 2 - MeasureTheory.predictableQuadraticVariation M 𝓕 μ n ω ∂μ at hzero
  rw [integral_sub (hM_two n).integrable_sq
    (_root_.Prove2MeSourceProof.h_dff4282bdbe72b40f691dd9d hΔ n)] at hzero
  have hz : (∫ _ω, (0 : ℝ) ^ 2 ∂μ) = 0 := by simp
  rw [hz] at hzero
  exact sub_eq_zero.mp hzero.symm
end Martingale

end MeasureTheory


