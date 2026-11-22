-- Prove2me | Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
-- name    : LeanPool_BooleanIsoperimetry_Macaulay
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:14:44.790516+00:00
-- url     : https://prove2.me/theorems/36906152-8696-4332-8caf-693d5d9e1aa7
-- title:
--   Macaulay
-- statement:
--   Definitions and structural lemmas for Macaulay, from Alexey Milovanov; Egor Lyfar; LeanPool contributors's pinned Boolean Isoperimetry and Conway--Guy Coherent Gaps development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped BigOperators
namespace BooleanIsoperimetry
noncomputable def HIncrement (n p : ℕ) : ℕ :=
  H n (p + 1) - H n p
noncomputable def macaulayShadowWeight {n : ℕ} (w : Cube n) : ℕ :=
  if h : w.Nonempty then (w.min' h : ℕ) else n + 1
noncomputable def cascadeBoundary (n x0 x1 : ℕ) : ℕ :=
  max (H n x0) x1 + max (H n x1) x0
noncomputable def pairedCascadeBoundary (n x0 x1 y0 y1 : ℕ) : ℕ :=
  cascadeBoundary n x0 x1 + cascadeBoundary n y0 y1
def cappedPrefixMass (n k l : ℕ) : ℕ :=
  min k (binomPrefix n l)
def splitPrefixMass (n a b l : ℕ) : ℕ :=
  cappedPrefixMass n a (l + 1) + cappedPrefixMass n b l
def CascadeInterleaves (n p q a b : ℕ) : Prop :=
  CascadeSplit n (a + b) p q ∧
  ∀ l, splitPrefixMass n a b l ≤ splitPrefixMass n p q l
end BooleanIsoperimetry


