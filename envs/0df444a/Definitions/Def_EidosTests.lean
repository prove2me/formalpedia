-- Prove2me | Definitions.Def_EidosTests
-- name    : EidosTests
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T23:37:05.431579+00:00
-- url     : https://prove2.me/theorems/74f4fceb-a5bd-4485-b8c8-20521d2f08d8
-- title:
--   Eidos Tests
-- statement:
--   Definitions and structural lemmas for Eidos Tests, from Lithos Protocol contributors's pinned Reserve accounting for an ErgoScript fragment development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/EidosTests.lean

import Definitions.Def_Eidos
set_option autoImplicit false
namespace Eidos.Tests
open Ergo Examples.Reserve
def context (selfValue : Long) (outputValues : List Long) : Context :=
  ⟨⟨selfValue⟩, outputValues.map Box.mk⟩
def hundred : Long := ⟨100000000000, by decide⟩
def thirty : Long := ⟨30000000000, by decide⟩
def twenty : Long := ⟨20000000000, by decide⟩
example : Accepts (script thirty) (context hundred [thirty]) := by decide
example : Accepts (script thirty) (context hundred [hundred]) := by decide
example : Accepts (script thirty) (context hundred [thirty, twenty, hundred]) := by decide
example : ¬ Accepts (script thirty) (context hundred [twenty]) := by decide
example : ¬ Accepts (script hundred) (context thirty [thirty]) := by decide
example : ¬ Accepts (script thirty) (context thirty [hundred]) := by decide
example : (script thirty).eval (context hundred []) =
    .error (.outputOutOfBounds 0) := by decide
example : ¬ Accepts (script thirty) (context hundred []) := by decide
example : (LongExpr.outputValue 3).eval (context hundred [thirty]) =
    .error (.outputOutOfBounds 3) := by decide
example : (Long.ofInt Long.minValue).map Subtype.val = .ok Long.minValue := by decide
example : (Long.ofInt Long.maxValue).map Subtype.val = .ok Long.maxValue := by decide
example : Long.ofInt (Long.maxValue + 1) = .error .arithmeticOverflow := by decide
example : Long.ofInt (Long.minValue - 1) = .error .arithmeticOverflow := by decide
def maxLong : Long := ⟨9223372036854775807, by decide⟩
def minLong : Long := ⟨-9223372036854775808, by decide⟩
def one : Long := ⟨1, by decide⟩
def negativeOne : Long := ⟨-1, by decide⟩
example : Long.sub maxLong negativeOne = .error .arithmeticOverflow := by decide
example : Long.sub minLong one = .error .arithmeticOverflow := by decide
example : (Long.sub twenty thirty).map Subtype.val = .ok (-10000000000) := by decide
example : (Long.sub hundred thirty).map Subtype.val = .ok 70000000000 := by decide
example : Accepts (script maxLong) (context maxLong [maxLong]) := by decide
def failingComparison : BoolExpr := .le (.outputValue 0) .selfValue
example : (BoolExpr.and (.const false) failingComparison).eval (context hundred []) =
    .ok false := by decide
example : (BoolExpr.and (.const true) failingComparison).eval (context hundred []) =
    .error (.outputOutOfBounds 0) := by decide
example : (BoolExpr.and failingComparison (.const false)).eval (context hundred []) =
    .error (.outputOutOfBounds 0) := by decide
example : (LongExpr.sub (.const maxLong) (.const negativeOne)).eval
    (context hundred []) = .error .arithmeticOverflow := by decide
end Eidos.Tests


