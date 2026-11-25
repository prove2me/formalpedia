-- Prove2me | Definitions.Def_SourceProof_308ca0aff4af17c75a3e2378
-- name    : SourceProof_308ca0aff4af17c75a3e2378
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:39:02.637843+00:00
-- url     : https://prove2.me/theorems/18508bb7-64ba-58b7-8550-5282ded16bb9
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integral_scale

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

theorem _root_.Prove2MeSourceProof.h_308ca0aff4af17c75a3e2378 (H : SimplePredictableRep F) (c : ℝ) (X : ℝ≥0 → Ω → ℝ) :
    (H.scale c).integral X = fun ω ↦ c * H.integral X ω := by
  funext ω
  change (c * H.initial ω) * X 0 ω + ∑ i : Fin H.partition.size,
    (c * H.coefficient i ω) * (X (H.partition.point i.succ ω) ω -
      X (H.partition.point i.castSucc ω) ω) =
    c * (H.initial ω * X 0 ω + ∑ i : Fin H.partition.size, H.coefficient i ω *
      (X (H.partition.point i.succ ω) ω - X (H.partition.point i.castSucc ω) ω))
  simp only [mul_add, mul_sum, mul_assoc]
end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


