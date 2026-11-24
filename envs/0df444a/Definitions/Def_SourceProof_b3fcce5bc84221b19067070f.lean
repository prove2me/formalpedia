-- Prove2me | Definitions.Def_SourceProof_b3fcce5bc84221b19067070f
-- name    : SourceProof_b3fcce5bc84221b19067070f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:11.097998+00:00
-- url     : https://prove2.me/theorems/4cdf275c-7f7f-43c8-aba1-d064d7518931
-- title:
--   StochLean source theorem: StochLean.contDiff_levyAreaBeta

import Definitions.Def_StochLean_ForMathlib_Analysis_LevyAreaRiccati_F000

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

theorem _root_.Prove2MeSourceProof.h_b3fcce5bc84221b19067070f (u T : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (levyAreaBeta u T) :=
  ((Real.contDiff_cosh.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))).log
    (fun t ↦ ne_of_gt (Real.cosh_pos (u * (T - t))))).neg
end StochLean


