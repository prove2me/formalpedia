-- Prove2me | Definitions.Def_MillerRabin_Lemmas
-- name    : MillerRabin_Lemmas
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T06:10:03.641048+00:00
-- url     : https://prove2.me/theorems/6dfe7452-16c7-47e3-b017-6ab1892dff30
-- title:
--   Lemmas
-- statement:
--   Definitions and structural lemmas for Lemmas, from hanwenzhu/miller-rabin contributors (see pinned LICENSE and source headers)'s pinned Miller–Rabin primality test error bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Lemmas.lean

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Field.Power
set_option autoImplicit false
open Nat
namespace ZMod
end ZMod
section FactLTNeZero
instance {n : ℕ} [hn : Fact (1 < n)] : NeZero (n - 1) := ⟨by have := hn.out; omega⟩
end FactLTNeZero


