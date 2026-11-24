-- Prove2me | Definitions.Def_SourceProof_19faa263b6d16ab54e81ed55
-- name    : SourceProof_19faa263b6d16ab54e81ed55
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:42.122269+00:00
-- url     : https://prove2.me/theorems/320a27ba-c9f0-460a-84bc-e430baed211a
-- title:
--   StochLean source theorem: MeasureTheory.integral_pathwiseQuadraticVariation_eq_predictableQuadraticVariation

import Definitions.Def_SourceProof_442b482eafb28142fd8f3cea
import Definitions.Def_SourceProof_8ea11dc318d9dadc642df2e6
import Definitions.Def_SourceProof_c0dcc82fc3fd86f95355f3d8
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


theorem _root_.Prove2MeSourceProof.h_19faa263b6d16ab54e81ed55
    {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [SigmaFiniteFiltration μ 𝓕] (hM : StronglyAdapted 𝓕 M)
    (hΔ : ∀ k, Integrable ((M (k + 1) - M k) ^ 2) μ) (n : ℕ) :
    ∫ ω, pathwiseQuadraticVariation M n ω ∂μ =
      ∫ ω, predictableQuadraticVariation M 𝓕 μ n ω ∂μ := by
  have hmart :=
    _root_.Prove2MeSourceProof.h_c0dcc82fc3fd86f95355f3d8 hM hΔ
  have hzero := hmart.setIntegral_eq (Nat.zero_le n) (s := Set.univ) MeasurableSet.univ
  simp only [Measure.restrict_univ, Pi.sub_apply,
    _root_.Prove2MeSourceProof.h_442b482eafb28142fd8f3cea, _root_.Prove2MeSourceProof.h_ce98c22b423cb6d74f7bb08a, Pi.zero_apply,
    sub_self, integral_zero] at hzero
  rw [integral_sub (_root_.Prove2MeSourceProof.h_8ea11dc318d9dadc642df2e6 hΔ n)
    (_root_.Prove2MeSourceProof.h_dff4282bdbe72b40f691dd9d hΔ n)] at hzero
  linarith
end MeasureTheory


