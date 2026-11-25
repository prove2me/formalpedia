-- Prove2me | Definitions.Def_AllOnesLab_Hard
-- name    : AllOnesLab_Hard
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T20:55:29.367815+00:00
-- url     : https://prove2.me/theorems/97e70b04-6102-4438-8ebf-e20b9a9ec2d8
-- title:
--   Hard
-- statement:
--   Definitions and structural lemmas for Hard, from Brandon M. Yates (BrandonMYates/allones-comparator; see pinned Apache-2.0 LICENSE and README.md)'s pinned All-ones polynomials over GF(2) under the quadratic substitution (OEIS A071642, TheoremDB P12771) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Hard.lean

import Definitions.Def_AllOnesLab_Trace
set_option autoImplicit true
open Polynomial
namespace AllOnesLab
section ASBasic
variable {K : Type*} [Field K]
noncomputable def asPoly (a : K) : K[X] := X ^ 2 + X + C a
end ASBasic
section ASTrace
variable {K : Type*} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]
end ASTrace
end AllOnesLab


