-- Prove2me | Definitions.Def_SourceProof_846c7b04e1b31171d517724f
-- name    : SourceProof_846c7b04e1b31171d517724f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:26:45.715414+00:00
-- url     : https://prove2.me/theorems/d0f21e88-3039-5893-902c-43e246fdb71c
-- title:
--   StochLean source theorem: StochLean.pathStieltjesIntegral_self_of_continuous

import Definitions.Def_SourceProof_7ed9f411faae98e0d913c0b8

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

theorem _root_.Prove2MeSourceProof.h_846c7b04e1b31171d517724f {T : ℝ≥0} {x : ℝ≥0 → ℝ}
    {hv : LocallyBoundedVariationOn x univ} {hr : ∀ t, ContinuousWithinAt x (Ici t) t}
    (hx : ContinuousOn x (Icc 0 T)) :
    pathStieltjesIntegral x hv hr x T = (x T ^ 2 + x 0 ^ 2) / 2 := by
  have hd (z : ℝ) : HasDerivAt (fun u : ℝ ↦ u ^ 2 / 2) z z := by
    have h := ((hasDerivAt_id z).pow 2).div_const 2
    change HasDerivAt (fun u : ℝ ↦ u ^ 2 / 2) ((2 * z ^ (2 - 1) * 1) / 2) z at h
    convert h using 1
    ring
  have h := _root_.Prove2MeSourceProof.h_7ed9f411faae98e0d913c0b8 (hv := hv) (hr := hr) hx hd continuous_id
  change StochLean.pathStieltjesIntegral x hv hr x T = x 0 * x 0 + (x T ^ 2 / 2 - x 0 ^ 2 / 2) at h
  rw [h]
  ring
end StochLean


