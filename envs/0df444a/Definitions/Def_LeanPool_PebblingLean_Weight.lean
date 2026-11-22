-- Prove2me | Definitions.Def_LeanPool_PebblingLean_Weight
-- name    : LeanPool_PebblingLean_Weight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:46:18.093335+00:00
-- url     : https://prove2.me/theorems/f30bb66b-ea3b-435d-a7fe-d9df1a9fe079
-- title:
--   Weight
-- statement:
--   Definitions and structural lemmas for Weight, from Lior Pachter; LeanPool contributors's pinned Optimal Pebbling Number of the Hypercube development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Weight.lean

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PebblingLean
universe u
namespace Pebbling
variable {V : Type u}
noncomputable def unitWeight (dist : V → V → ℕ) (target u : V) : ℚ :=
  (1 : ℚ) / (2 : ℚ) ^ dist u target
noncomputable def weight [Fintype V] (dist : V → V → ℕ) (D : Pebbling V) (target : V) : ℚ :=
  ∑ u, (D u : ℚ) * unitWeight dist target u
end Pebbling
end PebblingLean


