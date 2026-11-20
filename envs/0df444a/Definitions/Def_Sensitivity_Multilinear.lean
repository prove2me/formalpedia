-- Prove2me | Definitions.Def_Sensitivity_Multilinear
-- name    : Sensitivity_Multilinear
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T18:54:44.847342+00:00
-- url     : https://prove2.me/theorems/a71f92d0-c7df-4595-8c05-7762edb3a4f3
-- title:
--   Multilinear
-- statement:
--   Definitions and structural lemmas for Multilinear, from Samuel Schlesinger's pinned Boolean function sensitivity development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Multilinear.lean

import Definitions.Def_Sensitivity_Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Basic
set_option autoImplicit false
namespace Sensitivity
variable {n : ℕ}
def indicator (S : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ S)
def boolToInt (b : Bool) : ℤ := if b then 1 else 0
def BoolFun.moebius (f : BoolFun n) (S : Finset (Fin n)) : ℤ :=
  ∑ T ∈ S.powerset,
    (-1) ^ (S.card - T.card) * boolToInt (f (indicator T))
noncomputable def BoolFun.degree (f : BoolFun n) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => f.moebius S ≠ 0)).sup
    Finset.card
end Sensitivity


