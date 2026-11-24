-- Prove2me | Definitions.Def_SourceProof_220df0c636bc8e6794b6674d
-- name    : SourceProof_220df0c636bc8e6794b6674d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:47.864457+00:00
-- url     : https://prove2.me/theorems/380beb2c-9629-4557-91a2-4cf0a8ac45f0
-- title:
--   StochLean source theorem: StochLean.contDiff_levyAreaAlpha

import Definitions.Def_StochLean_ForMathlib_Analysis_LevyAreaRiccati_F000
import Definitions.Def_SourceProof_c00fcdab5be1893fe4dc345c

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

theorem _root_.Prove2MeSourceProof.h_220df0c636bc8e6794b6674d (u T : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (levyAreaAlpha u T) :=
  contDiff_const.mul (_root_.Prove2MeSourceProof.h_c00fcdab5be1893fe4dc345c.comp (contDiff_const.mul
    (contDiff_const.sub contDiff_id)))
end StochLean


