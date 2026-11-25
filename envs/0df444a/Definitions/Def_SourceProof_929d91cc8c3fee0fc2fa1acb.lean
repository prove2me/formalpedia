-- Prove2me | Definitions.Def_SourceProof_929d91cc8c3fee0fc2fa1acb
-- name    : SourceProof_929d91cc8c3fee0fc2fa1acb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:15:05.224152+00:00
-- url     : https://prove2.me/theorems/2f23191b-91a9-48fe-92a0-03f4b0733ab6
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.toProcess_combineOn

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F000
import Definitions.Def_SourceProof_335ae0b6c99b920a26294278
import Definitions.Def_SourceProof_45763a1547f08491c4364e73
import Definitions.Def_SourceProof_8f7895612117943074291d58
import Definitions.Def_SourceProof_a9c44e06617a4753cffd0417

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

theorem _root_.Prove2MeSourceProof.h_929d91cc8c3fee0fc2fa1acb (H K : SimplePredictableRep F) (ρ : StoppingTimePartition F)
    (φ : ℝ → ℝ → ℝ) (hφ : Measurable (Function.uncurry φ)) (h0 : φ 0 0 = 0) :
    (H.combineOn K ρ φ hφ).toProcess =
      fun t ω ↦ φ ((H.repartition ρ).toProcess t ω) ((K.repartition ρ).toProcess t ω) := by
  funext t ω
  by_cases ht : t = 0
  · subst t
    simp only [_root_.Prove2MeSourceProof.h_a9c44e06617a4753cffd0417]
    rfl
  by_cases hterm : t ≤ ρ.terminal ω
  · have hcell : ∃ i : Fin ρ.size, ρ.point i.castSucc ω < t ∧ t ≤ ρ.point i.succ ω :=
      (_root_.Prove2MeSourceProof.h_8f7895612117943074291d58 (ρ.path ω)) ⟨lt_of_le_of_ne bot_le (Ne.symm ht), hterm⟩
    obtain ⟨i, hi⟩ := hcell
    rw [(_root_.Prove2MeSourceProof.h_45763a1547f08491c4364e73 (i := i) (H.combineOn K ρ φ hφ)) hi,
      (_root_.Prove2MeSourceProof.h_45763a1547f08491c4364e73 (i := i) (H.repartition ρ)) hi,
      (_root_.Prove2MeSourceProof.h_45763a1547f08491c4364e73 (i := i) (K.repartition ρ)) hi]
    rfl
  · have hρt := lt_of_not_ge hterm
    rw [(_root_.Prove2MeSourceProof.h_335ae0b6c99b920a26294278 (H.combineOn K ρ φ hφ)) hρt,
      (_root_.Prove2MeSourceProof.h_335ae0b6c99b920a26294278 (H.repartition ρ)) hρt,
      (_root_.Prove2MeSourceProof.h_335ae0b6c99b920a26294278 (K.repartition ρ)) hρt, h0]
end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


