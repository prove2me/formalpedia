-- Prove2me | Definitions.Def_SumOfCubesPractice_cubeSum
-- name    : SumOfCubesPractice_cubeSum
-- status  : Definition
-- author  : @hacv16
-- created : 2026-10-16T14:57:27.064993+00:00
-- url     : https://prove2.me/theorems/581ea421-90bf-45c8-89ac-04681942bbea
-- title:
--   Sum of cubes
-- statement:
--   For every natural number $n$, define $$\operatorname{cubeSum}(n)=\sum_{k=1}^{n}k^3.$$ The sum includes both endpoints and is zero when $n=0$. This function represents the sum on the left side of the main identity.
-- source:
--   Requester-supplied mathematical statement for Sum of Cubes Identity (Practice); no external bibliographic source supplied. Definitions: cubeSum.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

namespace SumOfCubesPractice

def cubeSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, k ^ 3

end SumOfCubesPractice


