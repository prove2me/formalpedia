-- Prove2me | Definitions.Def_Sensitivity_Parity
-- name    : Sensitivity_Parity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T18:59:04.483573+00:00
-- url     : https://prove2.me/theorems/d7d0e0e1-9959-4f7a-ab61-bb3da3754739
-- title:
--   Parity
-- statement:
--   Definitions and structural lemmas for Parity, from Samuel Schlesinger's pinned Boolean function sensitivity development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Parity.lean

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum
set_option autoImplicit false
namespace Sensitivity
variable {n : ℕ}
def parity (x : Fin n → Bool) : ℤ :=
  (-1) ^ (Finset.univ.filter (fun i => x i)).card
def BoolFun.pmOne (f : BoolFun n) (x : Fin n → Bool) : ℤ :=
  if f x then 1 else -1
def BoolFun.paritySigned (f : BoolFun n) (x : Fin n → Bool) : ℤ :=
  f.pmOne x * parity x
end Sensitivity


