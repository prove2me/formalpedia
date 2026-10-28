-- Prove2me | solution 1 for AdDataSharing.Base.leave_deviation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:40:30.511059+00:00
-- url     : https://prove2.me/submissions/e07cbe60-0310-4bff-bd3f-c111ba5e16cf

import Mathlib
import Definitions.Def_AdDataSharing_Base_Model

open AdDataSharing.Base in
theorem solution (P : Params) (hP : P.Standing) (s s' : Bool) :
    payoffOpen P ⟨.adx2, false⟩ ⟨.adx1, s⟩ =
        P.α * P.M + (1 - 2 * P.α) * P.C - (1 - P.α) * P.w + P.η₁ * (P.C - P.w) ∧
      payoffOpen P ⟨.adx1, s'⟩ ⟨.adx1, s⟩ = (1 + P.η₂) * (P.C - P.w) ∧
      (payoffOpen P ⟨.adx2, false⟩ ⟨.adx1, s⟩ ≤ payoffOpen P ⟨.adx1, s'⟩ ⟨.adx1, s⟩ ↔
        NoLeave P) := by
  have e1 : payoffOpen P ⟨.adx2, false⟩ ⟨.adx1, s⟩ =
      P.α * P.M + (1 - 2 * P.α) * P.C - (1 - P.α) * P.w + P.η₁ * (P.C - P.w) := by
    simp only [payoffOpen, Bool.false_eq_true, ↓reduceIte]
  have e2 : payoffOpen P ⟨.adx1, s'⟩ ⟨.adx1, s⟩ = (1 + P.η₂) * (P.C - P.w) := by
    simp only [payoffOpen]
  refine ⟨e1, e2, ?_⟩
  rw [e1, e2]
  unfold NoLeave
  constructor <;> intro h <;> linarith
