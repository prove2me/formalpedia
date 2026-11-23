-- Prove2me | Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
-- name    : MillerRabin_Mathlib_Data_Fintype_Units
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T06:10:03.868431+00:00
-- url     : https://prove2.me/theorems/d1d5a5c0-4557-4634-a0e9-94401e169d16
-- title:
--   Units
-- statement:
--   Definitions and structural lemmas for Units, from hanwenzhu/miller-rabin contributors (see pinned LICENSE and source headers)'s pinned Miller–Rabin primality test error bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/Fintype/Units.lean

import Mathlib.Data.Fintype.Units
set_option autoImplicit false
instance ZMod.fintypeUnits (n : ℕ) : Fintype (ZMod n)ˣ :=
  if hn : n = 0 then
    hn ▸ UnitsInt.fintype
  else
    have : NeZero n := ⟨hn⟩
    inferInstance


