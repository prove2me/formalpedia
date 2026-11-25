-- Prove2me | Definitions.Def_SourceProof_87b09384855fcec7a9387831
-- name    : SourceProof_87b09384855fcec7a9387831
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:44:51.778417+00:00
-- url     : https://prove2.me/theorems/625f1b19-a07b-5b2a-b4da-1b4fb88fdb90
-- title:
--   StochLean source theorem: ProbabilityTheory.aemeasurable_compactDeviation_of_leftContinuous

import Definitions.Def_SourceProof_23795881371d33084b2010fb
import Definitions.Def_SourceProof_4a6ff19237aa56ae481190c2
import Definitions.Def_SourceProof_a307e422895411519841ce97
import Definitions.Def_SourceProof_b06b16ca7677673ce901dfe9

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Compact deviations for left-continuous paths

The initial value is included separately from the dense grid. Left continuity
on a half-line imposes no relation between that value and its right limit.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_87b09384855fcec7a9387831
    (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t))
    (hrX : ∀ᵐ ω ∂P, IsLeftContinuousPath (X · ω))
    (hrY : ∀ᵐ ω ∂P, IsLeftContinuousPath (Y · ω)) (T : ℝ≥0) :
    AEMeasurable (compactDeviation X Y T) P := by
  have hm := ((ENNReal.measurable_ofReal.comp ((hX 0).sub (hY 0)).norm).max
    (_root_.Prove2MeSourceProof.h_4a6ff19237aa56ae481190c2 (fun t ↦ ((hX t).sub (hY t)).norm) T)).aemeasurable
      (μ := P)
  apply hm.congr
  filter_upwards [hrX, hrY] with ω hx hy
  exact (_root_.Prove2MeSourceProof.h_23795881371d33084b2010fb hx hy).symm
end ProbabilityTheory


