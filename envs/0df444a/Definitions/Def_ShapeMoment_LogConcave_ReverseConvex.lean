-- Prove2me | Definitions.Def_ShapeMoment_LogConcave_ReverseConvex
-- name    : ShapeMoment_LogConcave_ReverseConvex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:14.346619+00:00
-- url     : https://prove2.me/theorems/15d4086b-ab15-46a7-9bb7-f6552696ba5f
-- title:
--   Feasible region of (Rev-Cvx)
-- statement:
--   For an $m\times n$ real matrix $A$, a vector $b$, and functions $f_p:\mathbb R^n\to\mathbb R$, the feasible region is
--
--   $$X=\{x:Ax=b,\ x_j\ge0\ (1\le j\le n),\ f_p(x)\le0\ (1\le p\le P)\}.$$
--
--   This is the general constraint system for the reverse convex optimization theorem. Convexity and regularity enter as hypotheses of Theorem 3.6.
-- source:
--   Chen, He, Jiang, Ryan & Zhang, The discrete moment problem with nonconvex shape constraints, arXiv:1708.02079v1, p. 10, (Rev-Cvx)

import Mathlib

namespace ShapeMoment.LogConcave

/-- Feasible points of the finite-dimensional reverse convex program (Rev-Cvx). -/
def revCvxFeasible {n m P : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (f : Fin P → (Fin n → ℝ) → ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ j, 0 ≤ x j) ∧ A.mulVec x = b ∧ ∀ p, f p x ≤ 0}

end ShapeMoment.LogConcave


