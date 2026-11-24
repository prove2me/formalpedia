-- Prove2me | Definitions.Def_SourceProof_fc5f89aed67e82971b1326cd
-- name    : SourceProof_fc5f89aed67e82971b1326cd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:14.662704+00:00
-- url     : https://prove2.me/theorems/05a56176-4fb6-47af-bd0d-2d14c661d679
-- title:
--   StochLean source theorem: StochLean.countable_pointAtomSet

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

theorem _root_.Prove2MeSourceProof.h_fc5f89aed67e82971b1326cd (μ : Measure T) [SFinite μ] : (pointAtomSet μ).Countable := by
  simpa only [StochLean.pointAtomSet, pos_iff_ne_zero] using
    (Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ)
      (fun t : T ↦ measurableSet_singleton t)
      (fun _ _ h ↦ disjoint_singleton.mpr h))
end StochLean


