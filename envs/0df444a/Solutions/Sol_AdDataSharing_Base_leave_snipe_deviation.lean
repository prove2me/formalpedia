-- Prove2me | solution 1 for AdDataSharing.Base.leave_snipe_deviation
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:39:48.734737+00:00
-- url     : https://prove2.me/submissions/86a46e77-3305-462c-96aa-7a406e6e5f5a

import Mathlib
import Definitions.Def_AdDataSharing_Base_Model
set_option autoImplicit false

open AdDataSharing.Base

theorem solution (P : Params) (hP : P.Standing) (s s' : Bool) :
    payoffOpen P ⟨.adx2, true⟩ ⟨.adx1, s⟩ =
        P.α * P.M + (1 - P.α) * P.C - 2 * (1 - P.α) * P.w + P.η₁ * (P.C - P.w) ∧
      payoffOpen P ⟨.adx1, s'⟩ ⟨.adx1, s⟩ = (1 + P.η₂) * (P.C - P.w) ∧
      (payoffOpen P ⟨.adx2, true⟩ ⟨.adx1, s⟩ ≤ payoffOpen P ⟨.adx1, s'⟩ ⟨.adx1, s⟩ ↔
        NoLeaveSnipe P) := by
  have h1 : payoffOpen P ⟨.adx2, true⟩ ⟨.adx1, s⟩ =
      P.α * P.M + (1 - P.α) * P.C - 2 * (1 - P.α) * P.w + P.η₁ * (P.C - P.w) := by
    simp [payoffOpen]
  have h2 : payoffOpen P ⟨.adx1, s'⟩ ⟨.adx1, s⟩ = (1 + P.η₂) * (P.C - P.w) := by
    simp [payoffOpen]
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  unfold NoLeaveSnipe
  constructor <;> intro h <;> nlinarith [h]
