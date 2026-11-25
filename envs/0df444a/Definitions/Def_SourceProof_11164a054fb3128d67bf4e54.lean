-- Prove2me | Definitions.Def_SourceProof_11164a054fb3128d67bf4e54
-- name    : SourceProof_11164a054fb3128d67bf4e54
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:30:54.151993+00:00
-- url     : https://prove2.me/theorems/9805aa7c-b362-4561-9ae2-2abbcf110f68
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.pointNat_withTop_mono

import Definitions.Def_SourceProof_73796dac7279446378b354de

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Discrete sampling on a source stopping-time partition

The finite ordered endpoint family is extended constantly after its last index. Its canonical
stopping sigma-fields and sampled process are then indexed by natural numbers, so the existing
discrete martingale and integral owners can be reused without a second finite-index calculus.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_11164a054fb3128d67bf4e54 (π : StoppingTimePartition F) :
    Monotone (fun n ↦ (π.pointNat n).withTop) := by
  intro n m hnm ω
  exact WithTop.coe_le_coe.mpr ((_root_.Prove2MeSourceProof.h_73796dac7279446378b354de π) ω hnm)
variable {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

variable [SigmaFiniteFiltration P F]

end ProbabilityTheory.StoppingTimePartition


