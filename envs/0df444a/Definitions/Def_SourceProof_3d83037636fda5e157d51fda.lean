-- Prove2me | Definitions.Def_SourceProof_3d83037636fda5e157d51fda
-- name    : SourceProof_3d83037636fda5e157d51fda
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:59:10.481051+00:00
-- url     : https://prove2.me/theorems/12f8fbbd-ef46-5bfd-a202-84c75d850266
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.toProcess_scale

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F002

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Algebra of the full source simple predictable class

The operations use actual common stopping-time refinements. Coefficients remain arbitrary
finite random variables, measurable at their left endpoints. Binary Borel operations fixing
`(0, 0)` preserve the class; in particular it is closed under addition and multiplication.
The elementary integral is bilinear, with its source initial term retained.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep

theorem _root_.Prove2MeSourceProof.h_3d83037636fda5e157d51fda (H : SimplePredictableRep F) (c : ℝ) :
    (H.scale c).toProcess = fun t ω ↦ c * H.toProcess t ω := by
  funext t ω
  change (if t = 0 then c * H.initial ω else ∑ i : Fin H.partition.size,
    if H.partition.point i.castSucc ω < t ∧ t ≤ H.partition.point i.succ ω
      then c * H.coefficient i ω else 0) = c * (ProbabilityTheory.SimplePredictableRep.toProcess H) t ω
  rw [ProbabilityTheory.SimplePredictableRep.toProcess]
  split_ifs with ht
  · rfl
  · rw [mul_sum]
    apply sum_congr rfl
    intro i _
    split_ifs
    · rfl
    · exact (mul_zero c).symm
end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


