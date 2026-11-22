-- Prove2me | Definitions.Def_Autoconvolutions_Digits
-- name    : Autoconvolutions_Digits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:47:46.757272+00:00
-- url     : https://prove2.me/theorems/223a4f07-f99b-47aa-847d-0a7431417c5e
-- title:
--   Digits
-- statement:
--   Definitions and structural lemmas for Digits, from Vjekoslav Kovač's pinned Sharpness for autoconvolutions development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Digits.lean

module
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Autoconvolutions.Digits
noncomputable def distinctFraction (r k : ℕ) : ℝ :=
  (r.descFactorial k : ℝ) / (r : ℝ) ^ k
end Autoconvolutions.Digits


