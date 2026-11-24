-- Prove2me | Definitions.Def_StochLean_ForMathlib_MeasureTheory_PointAtomicDecomposition_F000
-- name    : StochLean_ForMathlib_MeasureTheory_PointAtomicDecomposition_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:40.899595+00:00
-- url     : https://prove2.me/theorems/18ff33ac-2a68-4ef9-88e7-29cf9f770dc0
-- title:
--   StochLean: ForMathlib.MeasureTheory.PointAtomicDecomposition F000

import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

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

def pointAtomSet (μ : Measure T) : Set T := {t | μ {t} ≠ 0}
end StochLean


