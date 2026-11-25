-- Prove2me | Definitions.Def_DetDLP_D4RankCode
-- name    : DetDLP_D4RankCode
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:32:04.905716+00:00
-- url     : https://prove2.me/theorems/7820dc3f-6432-405b-8283-5fec7c11ead4
-- title:
--   Binary addresses for adaptive partial unrollings
-- statement:
--   An adaptive finite choice tree records a continuation for each local branch digit. Reading a fixed-width address consumes the ceiling logarithm of the local radix, rejecting invalid digits and nonzero trailing bits; a pathwise budget bounds the total number of bits consumed.

import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
namespace DetDLP.D4RankCode
/-- A node either emits a residual datum or asks for a digit of the indicated radix.
The continuation carries the entire worklist, so later radices can depend on earlier digits. -/
inductive Tree (α : Type) where
  | leaf (value : α)
  | choice (n : ℕ) (next : Fin n → Tree α)

namespace Tree
variable {α : Type}
/-- Fill unused ranks with zero, not with another copy of a valid contraction. -/
def read : Tree α → ℕ → ℕ → Option α
  | .leaf a, _,j => if j=0 then some a else none
  | .choice n f,b,j =>
    let w := Nat.clog 2 n
    if w ≤ b then
      if h : j % 2^w < n then read (f ⟨j%2^w,h⟩) (b-w) (j/2^w) else none
    else none

def Fits : Tree α → ℕ → Prop
  | .leaf _,_ => True
  | .choice n f,b => Nat.clog 2 n ≤ b ∧ ∀ i, Fits (f i) (b-Nat.clog 2 n)

noncomputable def total {R : Type} [AddCommMonoid R] (v : α → R) : Tree α → R
  | .leaf a => v a
  | .choice _ f => ∑ i, total v (f i)
end Tree
end DetDLP.D4RankCode


