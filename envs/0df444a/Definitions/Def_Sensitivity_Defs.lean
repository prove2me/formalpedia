-- Prove2me | Definitions.Def_Sensitivity_Defs
-- name    : Sensitivity_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T18:54:10.072403+00:00
-- url     : https://prove2.me/theorems/9ad75575-82da-4535-a003-b9d120f54da9
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Samuel Schlesinger's pinned Boolean function sensitivity development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/SamuelSchlesinger/sensitivity-conjecture/blob/9d2cff46ed11b43973a38d6150cf74dc8ab9a751/Sensitivity/Defs.lean

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
set_option autoImplicit false
namespace Sensitivity
abbrev BoolFun (n : ℕ) := (Fin n → Bool) → Bool
variable {n : ℕ}
def flipBit (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)
def BoolFun.sensitiveAt (f : BoolFun n) (x : Fin n → Bool) (i : Fin n) : Prop :=
  f (flipBit x i) ≠ f x
instance (f : BoolFun n) (x : Fin n → Bool) (i : Fin n) :
    Decidable (f.sensitiveAt x i) :=
  inferInstanceAs (Decidable (f (flipBit x i) ≠ f x))
def BoolFun.localSensitivity (f : BoolFun n) (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => f.sensitiveAt x i).card
noncomputable def BoolFun.sensitivity (f : BoolFun n) : ℕ :=
  Finset.univ.sup (fun x => f.localSensitivity x)
def flipCoords (x : Fin n → Bool) (S : Finset (Fin n)) : Fin n → Bool :=
  fun j => if j ∈ S then !x j else x j
end Sensitivity


