-- Prove2me | Definitions.Def_SPOBounds_StronglyConvex_StronglyConvexSet
-- name    : SPOBounds_StronglyConvex_StronglyConvexSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:36:31.131602+00:00
-- url     : https://prove2.me/theorems/0b9a69c7-7ae5-4ba7-81f5-54a2582ca190
-- title:
--   Normal cone $N_S(\bar w)$ and $\bar\mu$-strongly convex sets
-- statement:
--   Let $E$ be a real normed space with norm $\|\cdot\|$, and write $B(\bar w,r)=\{w:\|w-\bar w\|\le r\}$ for the closed ball. Cost vectors are continuous linear functionals $c$ on $E$, with $c^\top x$ denoting $c(x)$.
--
--   1. **Normal cone.** For $S\subseteq E$ and $\bar w\in S$,
--   $$N_S(\bar w) := \{c : c^\top(w-\bar w)\le 0 \text{ for all } w\in S\}.$$
--   2. **Strongly convex set.** For a constant $\bar\mu\ge0$, a convex set $S$ is $\bar\mu$-*strongly convex* with respect to $\|\cdot\|$ if for all $w_1,w_2\in S$ and all $\lambda\in[0,1]$,
--   $$B\Big(\lambda w_1+(1-\lambda)w_2,\ \Big(\frac{\bar\mu}{2}\Big)\lambda(1-\lambda)\|w_1-w_2\|^2\Big)\subseteq S.$$
--
--   Informally, every convex combination of two points of $S$ is surrounded by a ball in $S$ whose radius grows quadratically with the distance between the points. Examples include $\ell_q$ balls for $q\in(1,2]$ and sublevel sets of smooth strongly convex functions; a polytope is not strongly convex for any $\bar\mu>0$.
--
--   **Formalization Note** The predicate includes convexity of $S$, as Definition 5 is stated for convex sets, and quantifies $\lambda$ over $[0,1]$ only. The requirement $\bar\mu\ge0$ is carried by the theorems. The normal cone is defined for any point, but is only used at points of $S$. Mathlib's `StrongConvexOn` concerns functions and is not used.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 23 (§5.1, normal cone; Definition 5)

import Mathlib

namespace SPOBounds.StronglyConvex

/-- The normal cone of `S` at `w̄` (arXiv:1905.11488v3, §5.1, p. 23):
`N_S(w̄) = {c : cᵀ(w − w̄) ≤ 0 for all w ∈ S}`, with cost vectors as continuous linear
functionals (so `cᵀx` is `c x`). -/
def normalCone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (wbar : E) : Set (StrongDual ℝ E) :=
  {c | ∀ v ∈ S, c (v - wbar) ≤ 0}

/-- `μ̄`-strongly convex set (Definition 5, p. 23): `S` is convex and, for all `w₁, w₂ ∈ S` and
`λ ∈ [0, 1]`, the closed ball `B(λ w₁ + (1 − λ) w₂, (μ̄/2) λ (1 − λ) ‖w₁ − w₂‖²)` is contained
in `S`. The definition requires `μ̄ ≥ 0`; that is carried by the theorems. -/
def StronglyConvexSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μbar : ℝ) (S : Set E) : Prop :=
  Convex ℝ S ∧ ∀ w₁ ∈ S, ∀ w₂ ∈ S, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    Metric.closedBall (t • w₁ + (1 - t) • w₂) ((μbar / 2) * t * (1 - t) * ‖w₁ - w₂‖ ^ 2) ⊆ S

end SPOBounds.StronglyConvex


