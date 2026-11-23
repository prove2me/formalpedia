-- Prove2me | Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
-- name    : MillerRabin_Mathlib_Data_ZMod_Units
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T06:10:24.726803+00:00
-- url     : https://prove2.me/theorems/96245db1-bc1f-4c7b-989f-e959b54809f6
-- title:
--   Units
-- statement:
--   Definitions and structural lemmas for Units, from hanwenzhu/miller-rabin contributors (see pinned LICENSE and source headers)'s pinned Miller–Rabin primality test error bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Data/ZMod/Units.lean

import Mathlib.Data.ZMod.Units
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Basic
set_option autoImplicit false
namespace ZMod
def chineseRemainderₓ {m n : ℕ} (h : m.Coprime n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits
end ZMod


