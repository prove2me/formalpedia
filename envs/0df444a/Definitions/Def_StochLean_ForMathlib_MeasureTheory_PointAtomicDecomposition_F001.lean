-- Prove2me | Definitions.Def_StochLean_ForMathlib_MeasureTheory_PointAtomicDecomposition_F001
-- name    : StochLean_ForMathlib_MeasureTheory_PointAtomicDecomposition_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:15.98106+00:00
-- url     : https://prove2.me/theorems/4112ecfd-b962-4044-9063-b239ea676e69
-- title:
--   StochLean: ForMathlib.MeasureTheory.PointAtomicDecomposition F001

import Definitions.Def_StochLean_ForMathlib_MeasureTheory_PointAtomicDecomposition_F000

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

noncomputable def pointAtomicPart (μ : Measure T) : Measure T := μ.restrict (pointAtomSet μ)
noncomputable def pointDiffusePart (μ : Measure T) : Measure T := μ.restrict (pointAtomSet μ)ᶜ
end StochLean


