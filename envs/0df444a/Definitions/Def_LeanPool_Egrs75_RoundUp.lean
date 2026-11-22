-- Prove2me | Definitions.Def_LeanPool_Egrs75_RoundUp
-- name    : LeanPool_Egrs75_RoundUp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:26:21.054576+00:00
-- url     : https://prove2.me/theorems/b64ce5f5-e9e9-4237-a1e9-e673ee570e48
-- title:
--   Round Up
-- statement:
--   Definitions and structural lemmas for Round Up, from Egor Lyfar; LeanPool contributors's pinned The EGRS two-prime theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/RoundUp.lean

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Data.Finset.Attr
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Egrs75.RoundUp
open Nat
open Egrs75
variable (p : ℕ)
def ru (x : ℕ) : ℕ :=
  if x = 0 then 0
  else if x < p ∨ p < 3 then (if x ≤ (p - 1) / 2 then x else p)
  else
    if x % p ≤ (p - 1) / 2 then p * ru (x / p) + x % p
    else p * ru (x / p + 1)
termination_by x
decreasing_by
  · exact Nat.div_lt_self (by omega) (by omega)
  · -- x / p + 1 < x  when  p ≤ x  and  3 ≤ p (both from ¬(x < p ∨ p < 3))
    have hp3 : 3 ≤ p := by omega
    have _hpx : p ≤ x := by omega
    have hdiv : x / p ≤ x / 3 := Nat.div_le_div_left hp3 (by omega)
    have _hx3 : x / 3 + 1 < x := by omega
    omega
end Egrs75.RoundUp


