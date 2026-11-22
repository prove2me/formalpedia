-- Prove2me | Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
-- name    : LeanPool_BooleanIsoperimetry_Cascade
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:14:11.390045+00:00
-- url     : https://prove2.me/theorems/7f2f5ed7-6792-4e75-a7cb-a1dc2635641b
-- title:
--   Cascade
-- statement:
--   Definitions and structural lemmas for Cascade, from Alexey Milovanov; Egor Lyfar; LeanPool contributors's pinned Boolean Isoperimetry and Conway--Guy Coherent Gaps development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped BigOperators
namespace BooleanIsoperimetry
def IsBinomialCascade (n k r t : ℕ) : Prop :=
  r ≤ n + 1 ∧
  t ≤ Nat.choose n r ∧
  k = binomPrefix n r + t ∧
  (t < Nat.choose n r ∨ r = n + 1)
def cascadeSlice0Value (n r t : ℕ) : ℕ :=
  binomPrefix n r + (t - choosePred n r)
def cascadeSlice1Value (n r t : ℕ) : ℕ :=
  binomPrefix n (r - 1) + min t (choosePred n r)
def CascadeSplit (n k p q : ℕ) : Prop :=
  ∃ r t, IsBinomialCascade (n + 1) k r t ∧
    p = cascadeSlice0Value n r t ∧
    q = cascadeSlice1Value n r t
end BooleanIsoperimetry


