-- Prove2me | solution 1 for ABOThreshold.sparseProb_zero
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:31:26.491639+00:00
-- url     : https://prove2.me/submissions/740fdff8-e959-4fb9-af82-720a0d1610c5

import Definitions.Def_ABOThreshold_model

open ABOThreshold Finset

namespace Ag2Aux_ABOSparseZero

theorem sum0 (A : ℕ) (g : FaultPattern A 0 → ℝ) : ∑ p, g p = g true + g false :=
  (Fintype.sum_equiv (Equiv.refl Bool : FaultPattern A 0 ≃ Bool) g (fun b : Bool => g b)
    (fun _ => rfl)).trans (Fintype.sum_bool _)

end Ag2Aux_ABOSparseZero

open Ag2Aux_ABOSparseZero

theorem solution (A k : ℕ) (η : ℝ) : sparseProb A k η 0 = 1 - η := by
  unfold sparseProb
  rw [Finset.sum_filter]
  refine (sum0 A _).trans ?_
  simp [IsSparse, weight]
