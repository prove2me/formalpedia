-- Prove2me | Definitions.Def_SourceProof_ea6165ac1ae5d677ffaa10d7
-- name    : SourceProof_ea6165ac1ae5d677ffaa10d7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:51.176029+00:00
-- url     : https://prove2.me/theorems/98781190-0e8b-44db-9063-1df9203892ce
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.tendsto_top_of_separated_extended_samples

import Definitions.Def_SourceProof_8e6db4db0ea19e4e1d9e41fa

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Separated samples of a cadlag path cannot accumulate in finite time

Infinitely many chronologically ordered samples with a fixed positive consecutive
oscillation must escape every finite horizon. The contradiction uses the actual
finite left limit at a hypothetical accumulation point, not a compactness assumption
about a space of paths.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] {x : ℝ≥0 → E}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_ea6165ac1ae5d677ffaa10d7 (hx : IsCadlagPath x)
    {τ : ℕ → WithTop ℝ≥0} (hmono : Monotone τ)
    (hstrict : ∀ n, τ (n + 1) ≠ ⊤ → τ n < τ (n + 1)) {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ n, τ (n + 1) ≠ ⊤ → ε ≤ ‖x (τ (n + 1)).untopA - x (τ n).untopA‖) :
    Tendsto τ atTop (𝓝 ⊤) := by
  classical
  by_cases hex : ∃ N, τ N = ⊤
  · obtain ⟨N, hN⟩ := hex
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_antisymm (by rw [← hN]; exact hmono hn) le_top
  · have hne (n : ℕ) : τ n ≠ ⊤ := fun h ↦ hex ⟨n, h⟩
    let u : ℕ → ℝ≥0 := fun n ↦ (τ n).untopA
    have heq (n : ℕ) : (u n : WithTop ℝ≥0) = τ n := by
      change ((τ n).untopA : WithTop ℝ≥0) = τ n
      rw [WithTop.untopA_eq_untop (hne n), WithTop.coe_untop]
    have hu : StrictMono u := by
      apply strictMono_nat_of_lt_succ
      intro n
      apply WithTop.coe_lt_coe.mp
      rw [heq, heq]
      exact hstrict n (hne (n + 1))
    have hlim := (_root_.Prove2MeSourceProof.h_8e6db4db0ea19e4e1d9e41fa hx) hu hε (fun n ↦ hsep n (hne (n + 1)))
    have hcoe := WithTop.tendsto_coe_atTop.comp hlim
    change Tendsto (fun n ↦ (u n : WithTop ℝ≥0)) atTop (𝓝 ⊤) at hcoe
    simpa only [heq] using hcoe
end IsCadlagPath

end ProbabilityTheory


