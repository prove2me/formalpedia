-- Prove2me | Definitions.Def_SourceProof_8b8684e748d5e31b03d0af2c
-- name    : SourceProof_8b8684e748d5e31b03d0af2c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:58:20.032841+00:00
-- url     : https://prove2.me/theorems/121823ae-5e5f-487a-ba41-7c01c172847e
-- title:
--   StochLean source theorem: StochLean.pointDiffusePart_le

import Definitions.Def_StochLean_ForMathlib_MeasureTheory_PointAtomicDecomposition_F001

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The point-atomic and point-diffuse parts of an s-finite measure

The countable set of positive-mass singletons is intrinsic. Restriction to it
and to its complement gives the decomposition. On general measurable spaces,
having no point atoms is not asserted to exclude all nonsingleton atoms.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace StochLean

variable {T : Type*} [MeasurableSpace T] [MeasurableSingletonClass T]

omit [MeasurableSingletonClass T] in
theorem _root_.Prove2MeSourceProof.h_8b8684e748d5e31b03d0af2c (μ : Measure T) : pointDiffusePart μ ≤ μ := Measure.restrict_le_self
end StochLean


