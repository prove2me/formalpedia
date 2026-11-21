-- Prove2me | Definitions.Def_Eidos_Ergo_Long
-- name    : Eidos_Ergo_Long
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T23:35:50.2003+00:00
-- url     : https://prove2.me/theorems/924abb50-af91-4f41-8379-5cfa653396b2
-- title:
--   Long
-- statement:
--   Definitions and structural lemmas for Long, from Lithos Protocol contributors's pinned Reserve accounting for an ErgoScript fragment development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/Eidos/Ergo/Long.lean

import Std
set_option autoImplicit false
namespace Eidos.Ergo
deriving instance DecidableEq for Except
inductive EvalError where
  | arithmeticOverflow
  | outputOutOfBounds (index : Nat)
  deriving Repr, DecidableEq
abbrev Long := { n : Int // -9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807 }
namespace Long
def minValue : Int := -9223372036854775808
def maxValue : Int := 9223372036854775807
def ofInt (n : Int) : Except EvalError Long :=
  if h : minValue ≤ n ∧ n ≤ maxValue then .ok ⟨n, h⟩
  else .error .arithmeticOverflow
def sub (x y : Long) : Except EvalError Long := ofInt (x.val - y.val)
end Long
end Eidos.Ergo


