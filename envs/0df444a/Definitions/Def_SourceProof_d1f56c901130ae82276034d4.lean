-- Prove2me | Definitions.Def_SourceProof_d1f56c901130ae82276034d4
-- name    : SourceProof_d1f56c901130ae82276034d4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:27:43.551306+00:00
-- url     : https://prove2.me/theorems/34a83aea-ad47-4647-85c0-d067942d1fbf
-- title:
--   StochLean source theorem: StochLean.tendsto_stieltjesLeftSum_terminal

import Definitions.Def_SourceProof_09dae940366568ba50883f76
import Definitions.Def_SourceProof_e7dbbc237fa6384f486a8b07

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Left Riemann sums for pathwise Stieltjes integrals

The partial terminal cell is included, and the initial term is retained. Uniform
convergence holds on the whole horizon for continuous integrands, even when the
locally BV integrator has jumps. No nested-partition hypothesis is needed.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped NNReal Topology

namespace StochLean

variable {T : ℝ≥0}

variable {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

theorem _root_.Prove2MeSourceProof.h_d1f56c901130ae82276034d4 {π : ℕ → TimePartition T} {f : ℝ≥0 → ℝ}
    (hf : ContinuousOn f (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ f 0 * x 0 + ∑ i : Fin (π n).size, f ((π n).left i) * (π n).increment x i)
      atTop (𝓝 (pathStieltjesIntegral x hx hr f T)) := by
  have h := (_root_.Prove2MeSourceProof.h_e7dbbc237fa6384f486a8b07 (x := x) (hx := hx) (hr := hr) hf hmesh).tendsto_at
    (show T ∈ Icc 0 T from ⟨bot_le, le_rfl⟩)
  simpa only [_root_.Prove2MeSourceProof.h_09dae940366568ba50883f76] using h
end StochLean


