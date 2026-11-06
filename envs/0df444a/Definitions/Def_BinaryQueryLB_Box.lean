-- Prove2me | Definitions.Def_BinaryQueryLB_Box
-- name    : BinaryQueryLB_Box
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:52.377241+00:00
-- url     : https://prove2.me/theorems/0e44ed22-9367-4af4-a8c9-a7822c8305ab
-- title:
--   The box $X=[-R,R]^d$
-- statement:
--   For $R\in\mathbb R$, the **box** is $X=[-R,R]^d=\{y\in\mathbb R^d:\ |y_i|\le R\ \text{for every }i\}$.
--
--   All query points and all outputs of the algorithms lie in $X$.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Definition 2.1, p.11

import Mathlib

namespace BinaryQueryLB

/-- **The box `X = [−R, R]^d`.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Definition 2.1, p.11: "let `X = [−R, R]^d`".

**Formalization Note.** ℝ^d is `EuclideanSpace ℝ (Fin d)`, coordinates indexed from `0`. -/
def Box (d : ℕ) (R : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {y | ∀ i, |y i| ≤ R}

end BinaryQueryLB


