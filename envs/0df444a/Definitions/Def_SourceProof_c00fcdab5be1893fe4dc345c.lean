-- Prove2me | Definitions.Def_SourceProof_c00fcdab5be1893fe4dc345c
-- name    : SourceProof_c00fcdab5be1893fe4dc345c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:08:01.718718+00:00
-- url     : https://prove2.me/theorems/1531a698-14a5-4a4a-b491-2a2e3ccf9309
-- title:
--   StochLean source theorem: StochLean.contDiff_real_tanh

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The terminal Riccati coefficients for Levy's stochastic area

These are the actual smooth hyperbolic functions in Protter II.43, for every
real Fourier parameter, including zero and negative parameters. Their signs
on the backward time interval give the deterministic bound on the exponential.
No stochastic-area law or local-martingale conclusion is assumed here.
-/

@[expose] public section

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_c00fcdab5be1893fe4dc345c {n : WithTop ℕ∞} : ContDiff ℝ n Real.tanh := by
  rw [show Real.tanh = Real.sinh / Real.cosh from
    funext fun y ↦ Real.tanh_eq_sinh_div_cosh y]
  exact Real.contDiff_sinh.div Real.contDiff_cosh (fun x ↦ ne_of_gt (Real.cosh_pos x))
end StochLean


