-- Prove2me | Definitions.Def_SourceProof_c3fe4883c07b4b4f52cda50c
-- name    : SourceProof_c3fe4883c07b4b4f52cda50c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:58:22.758008+00:00
-- url     : https://prove2.me/theorems/2162473b-a8da-55b7-b282-f88b4bec2ece
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.sub_finset_lifetime_steps

import Definitions.Def_SourceProof_203c8143f8646ca99211fe57
import Definitions.Def_SourceProof_30748602910a669fc7d80008
import Definitions.Def_SourceProof_3eb335b1e032ebc9aabc0087
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite jump removal with bounded residual estimates

Only a fixed finite family of lifetime steps is removed. Its coefficients need not have
an integrable random jump count. A pathwise truncation by the original increment bound
is made before any conditional expectation is taken; no interchange of `min` and
conditional expectation is asserted.
-/

@[expose] public section

open Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*}

namespace IsCadlagPath

theorem _root_.Prove2MeSourceProof.h_c3fe4883c07b4b4f52cda50c {X : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hX : IsCadlagPath (X · ω)) (s : Finset ι)
    (τ : ι → Ω → WithTop ℝ≥0) (Z : ι → Ω → ℝ) :
    IsCadlagPath (fun t ↦ X t ω -
      ∑ i ∈ s, {v | τ i v ≤ (t : WithTop ℝ≥0)}.indicator (Z i) ω) :=
  (_root_.Prove2MeSourceProof.h_3eb335b1e032ebc9aabc0087 hX) (_root_.Prove2MeSourceProof.h_203c8143f8646ca99211fe57 s _
    (fun i _ ↦ _root_.Prove2MeSourceProof.h_30748602910a669fc7d80008 (τ i) (Z i) ω))
end IsCadlagPath

end ProbabilityTheory


