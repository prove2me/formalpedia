-- Prove2me | Definitions.Def_SourceProof_3af6edef675a4b05fcdc4190
-- name    : SourceProof_3af6edef675a4b05fcdc4190
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:39:15.70061+00:00
-- url     : https://prove2.me/theorems/56d14201-bcf9-46bf-ba94-25e8892945d1
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integral_combineOn_add

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F000

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

theorem _root_.Prove2MeSourceProof.h_3af6edef675a4b05fcdc4190 (H K : SimplePredictableRep F) (ρ : StoppingTimePartition F)
    (X : ℝ≥0 → Ω → ℝ) :
    (H.combineOn K ρ (· + ·) (measurable_fst.add measurable_snd)).integral X =
      fun ω ↦ (H.repartition ρ).integral X ω + (K.repartition ρ).integral X ω := by
  funext ω
  change (H.initial ω + K.initial ω) * X 0 ω +
    (∑ i : Fin ρ.size, ((H.repartition ρ).coefficient i ω +
      (K.repartition ρ).coefficient i ω) *
        (X (ρ.point i.succ ω) ω - X (ρ.point i.castSucc ω) ω)) =
    (H.initial ω * X 0 ω + ∑ i : Fin ρ.size, (H.repartition ρ).coefficient i ω *
      (X (ρ.point i.succ ω) ω - X (ρ.point i.castSucc ω) ω)) +
    (K.initial ω * X 0 ω + ∑ i : Fin ρ.size, (K.repartition ρ).coefficient i ω *
      (X (ρ.point i.succ ω) ω - X (ρ.point i.castSucc ω) ω))
  simp only [add_mul, sum_add_distrib]
  ring
end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


