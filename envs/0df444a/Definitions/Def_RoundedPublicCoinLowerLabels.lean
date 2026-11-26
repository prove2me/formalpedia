-- Prove2me | Definitions.Def_RoundedPublicCoinLowerLabels
-- name    : RoundedPublicCoinLowerLabels
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T17:53:58.187465+00:00
-- url     : https://prove2.me/theorems/7e76b3d6-8cda-436d-a6b6-d4c429989ce6
-- title:
--   Integer lower labels and coin depth in public-coin games
-- statement:
--   Defines local lower-label inequalities, the integer-grid recurrence obtained by rounding down at coin tosses, the maximum number of remaining coin tosses, and a restriction that treats omitted states as rejecting.
-- source:
--   Finite-horizon specialization of local reachability inequalities, https://arxiv.org/abs/1910.10636, with an integer rounding and coin-depth bound.

import Definitions.Def_RoundedPublicCoinGame

set_option autoImplicit false

namespace PvsNP.PublicGame

variable {S : Type}

/-- Only positive lower labels need to justify their value. A zero label
contributes nothing to the predecessor's bound, independently of the
game behind it. -/
def LowerLabels (G : Game S) (M H : ℕ) (u : ℕ → S → ℕ) : Prop :=
  ∀ r ≤ H, ∀ s, 2*u r s ≤ doubleUpdate G M u r s

/-- Solve the finite-horizon recurrence on the integer grid by rounding
down after each coin toss. Prover moves and terminal moves are exact. -/
def lowerValue (G : Game S) (M : ℕ) : ℕ → S → ℕ
  | 0, s => M*finish G s
  | r+1, s =>
    match G.move (r+1) s with
    | .stop b => if b then M else 0
    | .pick a b => max (lowerValue G M r a) (lowerValue G M r b)
    | .toss a b => (lowerValue G M r a + lowerValue G M r b)/2

/-- The maximum number of remaining fair coins on a branch of this game. -/
def coinDepth (G : Game S) : ℕ → S → ℕ
  | 0, _ => 0
  | r+1, s =>
    match G.move (r+1) s with
    | .stop _ => 0
    | .pick a b => max (coinDepth G r a) (coinDepth G r b)
    | .toss a b => max (coinDepth G r a) (coinDepth G r b) + 1

/-- A local checker is allowed to regard some positions as rejecting.
Such a restriction is useful even if the omitted subgames are large. -/
def trimGame (G : Game S) (keep : ℕ → S → Bool) : Game S where
  move r s := if keep r s then G.move r s else .stop false

end PvsNP.PublicGame


