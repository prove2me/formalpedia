-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFactsLe
-- name    : IntMul_Kappa_R8_Data_BitOppbankMoveFactsLe
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:57:16.341893+00:00
-- url     : https://prove2.me/theorems/935453a6-9801-450e-96c3-6402951ba3c0
-- title:
--   le_rank and le_eq_of_rank for nested idempotents
-- statement:
--   For nested idempotent matrices ($\mathrm{Le}\,A\,B$), one has $\mathrm{rank}\,A\le\mathrm{rank}\,B$ and $\mathrm{rank}(B-A)=\mathrm{rank}\,B-\mathrm{rank}\,A$. Equal rank forces $A=B$.
-- source:
--   R6 le_rank; NetLabels.rank_eq_trace_of_idem in Defs20

-- MoveFactsLe: le_rank / le_eq_of_rank for nested idempotents (pure matrix).

import Mathlib
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R6_Defs20
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

open Matrix
open NetLabels
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2

namespace IntMul.Kappa.R8.Bit.Oppbank.MoveFactsLe

theorem rank_idem {n : ℕ} {P : Matrix (Fin n) (Fin n) ℚ} (h : P * P = P) :
    (P.rank : ℚ) = P.trace :=
  NetLabels.rank_eq_trace_of_idem P h

theorem le_rank {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℚ}
    (hA : A * A = A) (hB : B * B = B) (h : Le A B) :
    A.rank ≤ B.rank ∧ (B - A).rank = B.rank - A.rank := by
  have hD := le_sub_idem hA hB h
  have e := rank_idem hD
  rw [Matrix.trace_sub, ← rank_idem hA, ← rank_idem hB] at e
  have hle : A.rank ≤ B.rank := by
    have : (0 : ℚ) ≤ (B.rank : ℚ) - A.rank := by rw [← e]; positivity
    exact_mod_cast (sub_nonneg.1 this)
  refine ⟨hle, ?_⟩
  have : ((B - A).rank : ℚ) = ((B.rank - A.rank : ℕ) : ℚ) := by rw [e, Nat.cast_sub hle]
  exact_mod_cast this

theorem le_eq_of_rank {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℚ}
    (hA : A * A = A) (hB : B * B = B) (h : Le A B) (hr : B.rank ≤ A.rank) : B = A := by
  have h0 : (B - A).rank = 0 := by rw [(le_rank hA hB h).2]; omega
  have h1 : LinearMap.range (B - A).mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 h0
  have h2 : (B - A).mulVecLin = 0 := LinearMap.range_eq_bot.1 h1
  have : B - A = 0 := by
    ext i j
    have := congrArg (fun f => f (Pi.single j 1) i) h2
    simpa [Matrix.mulVec_single] using this
  exact sub_eq_zero.1 this

end IntMul.Kappa.R8.Bit.Oppbank.MoveFactsLe


