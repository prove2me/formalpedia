-- Prove2me | Definitions.Def_LeanPool_PebblingLean_FiniteProbability
-- name    : LeanPool_PebblingLean_FiniteProbability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:45:53.086006+00:00
-- url     : https://prove2.me/theorems/4f6dedf0-3d4d-4cd1-92f9-f1ffc1151b0c
-- title:
--   Finite Probability
-- statement:
--   Definitions and structural lemmas for Finite Probability, from Lior Pachter; LeanPool contributors's pinned Optimal Pebbling Number of the Hypercube development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/FiniteProbability.lean

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PebblingLean
namespace FiniteProbability
variable {Ω ι : Type*}
noncomputable def uniformProbability [Fintype Ω] (P : Ω → Prop) [DecidablePred P] : ℚ :=
  ((Finset.univ.filter P).card : ℚ) / (Fintype.card Ω : ℚ)
noncomputable def uniformExpectation [Fintype Ω] (X : Ω → ℕ) : ℚ :=
  (∑ ω : Ω, (X ω : ℚ)) / (Fintype.card Ω : ℚ)
end FiniteProbability
end PebblingLean


