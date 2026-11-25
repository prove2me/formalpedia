-- Prove2me | Definitions.Def_SourceProof_0a4c4ca9908aae52a5fd404b
-- name    : SourceProof_0a4c4ca9908aae52a5fd404b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:35:41.473409+00:00
-- url     : https://prove2.me/theorems/43b6a831-c989-41eb-ad0c-b3c426e3c138
-- title:
--   StochLean source theorem: StochLean.continuous_frechetTaylorErrorCoefficient_of_contDiff

import Definitions.Def_StochLean_ForMathlib_Analysis_FrechetTaylorCoefficient_F000
import Definitions.Def_SourceProof_73d7ede32c630ae6f4b43125

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # A continuous diagonal-zero coefficient for the Frechet Taylor error

Dividing the actual second-order error by the squared increment norm gives
a coefficient continuous even on the diagonal. This makes the jump-separation
argument applicable to vector paths without a discontinuous directional choice.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}

theorem _root_.Prove2MeSourceProof.h_0a4c4ca9908aae52a5fd404b (hf : ContDiff ℝ 2 f) :
    Continuous (fun p : E × E ↦ frechetTaylorErrorCoefficient f p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact _root_.Prove2MeSourceProof.h_73d7ede32c630ae6f4b43125 hf
    continuous_fst.continuousAt continuous_snd.continuousAt
end StochLean


