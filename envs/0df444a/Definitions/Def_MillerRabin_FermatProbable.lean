-- Prove2me | Definitions.Def_MillerRabin_FermatProbable
-- name    : MillerRabin_FermatProbable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:59:28.358291+00:00
-- url     : https://prove2.me/theorems/f3a366ba-9633-405a-93ce-1a184db2f8dc
-- title:
--   Fermat Probable
-- statement:
--   Definitions and structural lemmas for Fermat Probable, from hanwenzhu/miller-rabin contributors (see pinned LICENSE and source headers)'s pinned Miller–Rabin primality test error bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/FermatProbable.lean

import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
set_option autoImplicit false
open Nat
def FPP (n : ℕ) (a : ZMod n) : Prop :=
  a ^ (n - 1) = 1
namespace FPP
instance decidable {n : ℕ} {a : ZMod n} : Decidable (FPP n a) :=
  decEq _ _
abbrev Carmichael (n : ℕ) : Prop :=
  ∀ a : (ZMod n)ˣ, FPP n a
namespace Carmichael
variable {n : ℕ}
end Carmichael
end FPP


