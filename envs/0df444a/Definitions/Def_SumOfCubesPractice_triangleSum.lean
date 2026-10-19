-- Prove2me | Definitions.Def_SumOfCubesPractice_triangleSum
-- name    : SumOfCubesPractice_triangleSum
-- status  : Definition
-- author  : @hacv16
-- created : 2026-10-16T14:57:17.19575+00:00
-- url     : https://prove2.me/theorems/55a0f607-97bf-427b-9d35-18e0a9a8c149
-- title:
--   Triangular sum
-- statement:
--   For every natural number $n$, define $$\operatorname{triangleSum}(n)=\sum_{k=1}^{n}k.$$ The sum includes both endpoints and is zero when $n=0$. This function provides the shared sum of positive integers used in the three theorem statements.
-- source:
--   Requester-supplied mathematical statement for Sum of Cubes Identity (Practice); no external bibliographic source supplied. Definitions: triangleSum.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

namespace SumOfCubesPractice

def triangleSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, k

end SumOfCubesPractice


