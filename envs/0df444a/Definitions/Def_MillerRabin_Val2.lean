-- Prove2me | Definitions.Def_MillerRabin_Val2
-- name    : MillerRabin_Val2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T06:10:01.827811+00:00
-- url     : https://prove2.me/theorems/70bdee95-d663-419c-bf76-418cb830e3dd
-- title:
--   Val2
-- statement:
--   Definitions and structural lemmas for Val2, from hanwenzhu/miller-rabin contributors (see pinned LICENSE and source headers)'s pinned Miller–Rabin primality test error bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Val2.lean

import Mathlib.NumberTheory.Padics.PadicVal.Basic
set_option autoImplicit false
open Nat
section NatEqTwoPowMulOdd
abbrev val₂ (n : ℕ) : ℕ :=
  padicValNat 2 n
abbrev oddPart (n : ℕ) : ℕ :=
  n / 2 ^ val₂ n
variable {n : ℕ}
variable {m : ℕ}
end NatEqTwoPowMulOdd


