-- Prove2me | Definitions.Def_SourceProof_2f8153518021639b8e8e83d5
-- name    : SourceProof_2f8153518021639b8e8e83d5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:50.622388+00:00
-- url     : https://prove2.me/theorems/e8b6db49-1e51-4879-a057-b633cccd2556
-- title:
--   StochLean source theorem: StochLean.pointAtomicPart_add_pointDiffusePart

import Definitions.Def_StochLean_ForMathlib_MeasureTheory_PointAtomicDecomposition_F001
import Definitions.Def_SourceProof_fc5f89aed67e82971b1326cd

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

theorem _root_.Prove2MeSourceProof.h_2f8153518021639b8e8e83d5 (μ : Measure T) [SFinite μ] :
    pointAtomicPart μ + pointDiffusePart μ = μ :=
  Measure.restrict_add_restrict_compl (_root_.Prove2MeSourceProof.h_fc5f89aed67e82971b1326cd μ).measurableSet
end StochLean


