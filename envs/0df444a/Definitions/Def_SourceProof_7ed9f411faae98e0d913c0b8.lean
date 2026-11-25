-- Prove2me | Definitions.Def_SourceProof_7ed9f411faae98e0d913c0b8
-- name    : SourceProof_7ed9f411faae98e0d913c0b8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:24:16.648795+00:00
-- url     : https://prove2.me/theorems/3e64aa32-9687-4e12-936b-cacd98391d31
-- title:
--   StochLean source theorem: StochLean.pathStieltjesIntegral_chain_rule

import Definitions.Def_SourceProof_a3e9660b6c7c895b0c4c58de

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # C1 change of variables along a continuous finite-variation path

The first-order remainders are bounded by their derivative oscillation times
the path variation. Actual left Riemann sums identify the Stieltjes integral.
The increment formula excludes the separately owned source initial term.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped NNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_7ed9f411faae98e0d913c0b8 {T : ℝ≥0} {x : ℝ≥0 → ℝ}
    {hv : LocallyBoundedVariationOn x univ} {hr : ∀ t, ContinuousWithinAt x (Ici t) t}
    (hx : ContinuousOn x (Icc 0 T))
    {φ φ' : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ' z) z) (hc : Continuous φ') :
    pathStieltjesIntegral x hv hr (fun t ↦ φ' (x t)) T =
      φ' (x 0) * x 0 + (φ (x T) - φ (x 0)) := by
  rw [StochLean.pathStieltjesIntegral, _root_.Prove2MeSourceProof.h_a3e9660b6c7c895b0c4c58de hx hφ hc]
end StochLean


