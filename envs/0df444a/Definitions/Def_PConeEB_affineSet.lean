-- Prove2me | Definitions.Def_PConeEB_affineSet
-- name    : PConeEB_affineSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:00.622705+00:00
-- url     : https://prove2.me/theorems/9a89e6f6-59e2-45e3-a774-cd0d032e236e
-- title:
--   The affine set $\mathcal L + a$
-- statement:
--   For a subspace $\mathcal L\subseteq\mathcal E$ and a point $a\in\mathcal E$, the affine set of the conic feasibility problem (Feas) is
--   $$
--   \mathcal L+a=\{x\in\mathcal E: x-a\in\mathcal L\}.
--   $$
--   The problem (Feas) asks for a point of $(\mathcal L+a)\cap K$.
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, (Feas), p.1

import Mathlib

namespace PConeEB

/-- The affine set `L + a`, for a subspace `L` and a point `a`, of the feasibility problem (Feas).
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, (Feas), p.1. -/
def affineSet {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℝ E) (a : E) : Set E :=
  {x | x - a ∈ L}

end PConeEB


