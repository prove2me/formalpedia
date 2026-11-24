-- Prove2me | Definitions.Def_SourceProof_43fbf96de532b2e4c5ed2cd2
-- name    : SourceProof_43fbf96de532b2e4c5ed2cd2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:47.392409+00:00
-- url     : https://prove2.me/theorems/c52a88c1-e6ac-4be8-99fb-c28491e1b1d2
-- title:
--   StochLean source theorem: ProbabilityTheory.tendstoUCP_of_subseq_ae_compactDeviation_of_aemeasurable

import Definitions.Def_SourceProof_53d90595c026ce14255ca40b

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Uniform path convergence and a subsequence criterion for UCP

Measurability of the output compact deviations is explicit in the converse.
No continuity of an outer measure on arbitrary decreasing sets is used.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem _root_.Prove2MeSourceProof.h_43fbf96de532b2e4c5ed2cd2 [IsFiniteMeasure P]
    {X : ℕ → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}
    (hm : ∀ n T, AEMeasurable (compactDeviation (X n) Y T) P)
    (hXY : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ k : ℕ → ℕ,
      ∀ᵐ ω ∂P, ∀ T, Tendsto (fun n ↦ compactDeviation (X (ns (k n))) Y T ω) atTop (𝓝 0)) :
    TendstoUCP P X atTop Y := by
  intro T ε hε
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨k, hk⟩ := hXY ns hns
  exact ⟨k, _root_.Prove2MeSourceProof.h_53d90595c026ce14255ca40b
    (fun n T ↦ hm (ns (k n)) T) hk T ε hε⟩
end ProbabilityTheory


