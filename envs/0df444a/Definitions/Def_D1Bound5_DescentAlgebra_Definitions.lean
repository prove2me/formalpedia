-- Prove2me | Definitions.Def_D1Bound5_DescentAlgebra_Definitions
-- name    : D1Bound5_DescentAlgebra_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:33:56.080435+00:00
-- url     : https://prove2.me/theorems/9a20b6bc-5ec9-4ed4-86ca-1c0333be3fb4
-- title:
--   Descent Algebra
-- statement:
--   The plus transformation in (sm:bs7-mutation). Changing the sign of one chosen square root gives the minus transformation. The named objects in this bundle include `mutate`.
-- source:
--   D1Bound5/DescentAlgebra.lean, lines 6-9, SHA-256 cdc9699d8936a77fc1a6ff59d54b2a5e92fe962a175e2215e62e2e02b8375486. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.LinearCombination

section
namespace D1Bound5

/-- The plus transformation in (sm:bs7-mutation). Changing the sign of one
chosen square root gives the minus transformation. -/
def mutate {R : Type*} [CommRing R] (a b z r0 r s : R) : R :=
  a+b+(2*a*b+1)*z+2*r0*r*s







end D1Bound5
end


