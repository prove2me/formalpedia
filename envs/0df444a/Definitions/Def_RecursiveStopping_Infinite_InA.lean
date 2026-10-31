-- Prove2me | Definitions.Def_RecursiveStopping_Infinite_InA
-- name    : RecursiveStopping_Infinite_InA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:41:25.888655+00:00
-- url     : https://prove2.me/theorems/b3962194-6592-4b90-be2c-53b3e92e5efd
-- title:
--   The space $\mathcal A_d$
-- statement:
--   $$
--   \mathcal A_d:=\big\{f\in C(\mathbb R^d;\mathbb R_+):\ \|f\|_{\mathcal A_d}<\infty\big\},
--   $$
--
--   the continuous non-negative functions on $\mathbb R^d$ with at most linear growth. The value function of the recursive stopping problem is sought in this set.
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, (8), p.8

import Mathlib
import Definitions.Def_RecursiveStopping_Infinite_wnorm

open scoped NNReal ENNReal

namespace RecursiveStopping.Infinite

/-- Membership in the space `A_d` of Colaneri & De Angelis, arXiv:1905.02650v4, (8), p.8:
$$A_d := \{ f : f\in C(\mathbb R^d;\mathbb R_+),\ \|f\|_{A_d}<\infty\}.$$
`InA f` holds when `f : ℝ^d → ℝ` is continuous, non-negative and has finite weighted norm. -/
def InA {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  Continuous f ∧ (∀ x, 0 ≤ f x) ∧ wnorm f < ⊤

end RecursiveStopping.Infinite


