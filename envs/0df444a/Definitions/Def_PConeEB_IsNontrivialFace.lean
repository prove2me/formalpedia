-- Prove2me | Definitions.Def_PConeEB_IsNontrivialFace
-- name    : PConeEB_IsNontrivialFace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:14.068517+00:00
-- url     : https://prove2.me/theorems/489e18c6-0d25-4cf7-8ec3-abe2ff9e7c1e
-- title:
--   Nontrivial face
-- statement:
--   A face $\mathcal F$ of a cone $K$ is **nontrivial** if $\mathcal F\ne K$ and $\mathcal F\ne K\cap-K$.
--
--   **Formalization Note** The set $K\cap-K$ is written $\{x: x\in K,\ -x\in K\}$; it equals $\{0\}$ exactly when $K$ is pointed. This predicate is applied to the exposed face $K\cap\{z\}^\perp$, with $z\in K^*$.
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, §2, p.3

import Mathlib

namespace PConeEB

/-- A face `F` of a cone `K` is nontrivial if `F ≠ K` and `F ≠ K ∩ -K`.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, §2, p.3.

**Formalization Note.** `K ∩ -K` is written `{x | x ∈ K ∧ -x ∈ K}`. It differs from `{0}` when `K`
is not pointed. -/
def IsNontrivialFace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K F : Set E) : Prop :=
  F ≠ K ∧ F ≠ {x | x ∈ K ∧ -x ∈ K}

end PConeEB


