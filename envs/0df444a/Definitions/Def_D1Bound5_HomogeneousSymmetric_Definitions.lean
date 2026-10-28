-- Prove2me | Definitions.Def_D1Bound5_HomogeneousSymmetric_Definitions
-- name    : D1Bound5_HomogeneousSymmetric_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:30:51.231289+00:00
-- url     : https://prove2.me/theorems/89158397-8bde-4084-bc03-b4cb31f09ad5
-- title:
--   Homogeneous Symmetric
-- statement:
--   The value of the complete homogeneous symmetric polynomial as an explicit sum over degree-n multisets. No distinctness assumptions are needed. The named objects in this bundle include `homogeneousMultisetSum`.
-- source:
--   D1Bound5/HomogeneousSymmetric.lean, lines 8-13, SHA-256 9ca0c1b5630feef5d0a34c972d9c43d84be51f3ce74b855f5c9873ea76bd8466. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Sym.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

section
open Finset Multiset Sym

namespace D1Bound5

/-- The value of the complete homogeneous symmetric polynomial as an explicit
sum over degree-n multisets. No distinctness assumptions are needed. -/
def homogeneousMultisetSum
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    (a : ι → R) (n : ℕ) : R :=
  ∑ t : Sym ι n, (t.1.map a).prod













end D1Bound5
end


