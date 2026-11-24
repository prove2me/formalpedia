-- Prove2me | Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
-- name    : SourceProof_60b183cce884b1ffa7a599f8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:59:32.212887+00:00
-- url     : https://prove2.me/theorems/c201d21b-8216-4253-8e6d-35c2d3ab3ce1
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.hasCadlagPaths

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Semimartingales as good integrators

The canonical predicate is zero-sequential continuity of the elementary
integral for uniform convergence in `(t,ω)`. The epsilon/delta source
continuity criterion is proved equivalent. Classical decompositions are not
part of this definition. This file does not select a stochastic integral for
general caglad integrands or a quadratic variation.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable {X : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

namespace IsSemimartingale

theorem _root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 (hX : IsSemimartingale X F P) : HasCadlagPaths X P := by
  have hreg : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ProbabilityTheory.IsCadlagPath (fun t ↦ stoppedProcess X (fun _ ↦ ((n : ℝ≥0) : WithTop ℝ≥0)) t ω) :=
    ae_all_iff.mpr fun n ↦ (hX n).2.1
  filter_upwards [hreg] with ω hω
  have heq : ∀ t : ℝ≥0, ∃ n : ℕ,
      (fun s ↦ stoppedProcess X (fun _ ↦ ((n : ℝ≥0) : WithTop ℝ≥0)) s ω) =ᶠ[𝓝 t]
        fun s ↦ X s ω := by
    intro t
    obtain ⟨n, hn⟩ := exists_nat_gt t
    refine ⟨n, ?_⟩
    filter_upwards [Iio_mem_nhds hn] with s hs
    exact stoppedProcess_eq_of_le (WithTop.coe_le_coe.mpr hs.le)
  constructor
  · intro t
    obtain ⟨n, hn⟩ := heq t
    exact ((hω n).1 t).congr_of_eventuallyEq
      (hn.symm.filter_mono nhdsWithin_le_nhds) hn.self_of_nhds.symm
  · intro t ht
    obtain ⟨n, hn⟩ := heq t
    obtain ⟨a, ha⟩ := (hω n).2 t ht
    exact ⟨a, ha.congr' (hn.filter_mono nhdsWithin_le_nhds)⟩
end IsSemimartingale

end ProbabilityTheory


