-- Prove2me | Definitions.Def_SourceProof_e7dbbc237fa6384f486a8b07
-- name    : SourceProof_e7dbbc237fa6384f486a8b07
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:17:58.960031+00:00
-- url     : https://prove2.me/theorems/2a4a36f5-7220-4446-bc4b-d9e0e77cda49
-- title:
--   StochLean source theorem: StochLean.tendstoUniformlyOn_stieltjesLeftSum

import Definitions.Def_SourceProof_0a747dfdc63dcf3edfcb5081
import Definitions.Def_SourceProof_592358001a7c02aa8319b535
import Definitions.Def_SourceProof_bfe1ba329ac07d8c42184d5a
import Definitions.Def_SourceProof_c3eab2187d68c022ae90ef4e
import Definitions.Def_SourceProof_f72cde5ffb5df7e2856ca7ba

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

theorem _root_.Prove2MeSourceProof.h_e7dbbc237fa6384f486a8b07 {π : ℕ → TimePartition T} {f : ℝ≥0 → ℝ}
    (hf : ContinuousOn f (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n ↦ stieltjesLeftSum (π n) x f)
      (pathStieltjesIntegral x hx hr f) atTop (Icc 0 T) := by
  have h := _root_.Prove2MeSourceProof.h_592358001a7c02aa8319b535
    (fun n ↦ _root_.Prove2MeSourceProof.h_f72cde5ffb5df7e2856ca7ba (x := x) (hx := hx) (hr := hr) (π n) f T)
    (_root_.Prove2MeSourceProof.h_bfe1ba329ac07d8c42184d5a hf)
    (_root_.Prove2MeSourceProof.h_0a747dfdc63dcf3edfcb5081 hf hmesh)
  simpa only [_root_.Prove2MeSourceProof.h_c3eab2187d68c022ae90ef4e] using h
end StochLean


