-- Prove2me | Definitions.Def_AnchoredEP_IterState
-- name    : AnchoredEP_IterState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:34:57.764195+00:00
-- url     : https://prove2.me/theorems/04c08b27-bf7b-44a4-8060-e6cd9997bff0
-- title:
--   State $(z_k,v_k,A_k)$ of an outer iteration
-- statement:
--   At the start of outer iteration $k$, Algorithm 3 holds the iterate $z_k\in\mathbb R^d$, the vector $v_k\in\mathbb R^d$ associated with $H$, and the cumulative step size $A_k\in\mathbb R$.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Algorithm 3, p.37

import Mathlib

namespace AnchoredEP

/-- **The state of Algorithm 3 at the start of an outer iteration.** Jiang–Yoon,
arXiv:2609.30212, Algorithm 3, p.37: at outer iteration `k` the method holds the iterate `z_k`,
the vector `v_k ∈ H(z_k)` and the cumulative step size `A_k`. -/
structure IterState (d : ℕ) where
  /-- the iterate `z_k` -/
  z : EuclideanSpace ℝ (Fin d)
  /-- the vector `v_k` associated with `H` -/
  v : EuclideanSpace ℝ (Fin d)
  /-- the cumulative step size `A_k` -/
  A : ℝ

end AnchoredEP


