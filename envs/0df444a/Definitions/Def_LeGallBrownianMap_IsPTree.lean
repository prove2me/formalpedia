-- Prove2me | Definitions.Def_LeGallBrownianMap_IsPTree
-- name    : LeGallBrownianMap_IsPTree
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:05.285145+00:00
-- url     : https://prove2.me/theorems/3d7ad720-d872-4e86-aa26-5962321477c4
-- title:
--   Plane trees and $p$-trees
-- statement:
--   A **plane tree** is a finite set $\tau$ of words such that (i) $\varnothing\in\tau$; (ii) the parent $(u_1,\dots,u_{k-1})$ of every $v=(u_1,\dots,u_k)\in\tau$, $k\ge1$, is in $\tau$; (iii) for every $v\in\tau$ there is $k_v(\tau)\ge0$ with $vj\in\tau$ iff $1\le j\le k_v(\tau)$. The generation of $v$ is its length $|v|$. For a fixed integer $p\ge2$, a **$p$-tree** is a plane tree in which every vertex of odd generation has exactly $p-1$ children.
--
--   Vertices of even generation are white, those of odd generation black; $p$-trees with labels code the $2p$-angulations through the BDG bijection.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.1, p.8

import Mathlib
import Definitions.Def_LeGallBrownianMap_numChildren

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.1, p.8:
"A plane tree τ is a finite subset of the set U = ⋃_{n=0}^∞ ℕ^n of all finite sequences of
positive integers (including the empty sequence ∅), which satisfies the three following
conditions: (i) ∅ ∈ τ; (ii) for every v = (u_1, ..., u_k) ∈ τ with k ≥ 1, the sequence
(u_1, ..., u_{k−1}) also belongs to τ […]; (iii) for every v = (u_1, ..., u_k) ∈ τ there exists an
integer k_v(τ) ≥ 0 such that, for every j ∈ ℕ, the vertex vj := (u_1, ..., u_k, j) belongs to τ if
and only if 1 ≤ j ≤ k_v(τ) […]. Throughout this work, the integer p ≥ 2 is fixed. A p-tree is a
plane tree τ that satisfies the following additional property: For every v ∈ τ such that |v| is
odd, k_v(τ) = p − 1."

**Formalization Note.** Vertices are `List ℕ+`; the generation `|v|` is the length; `v ++ [j]` is
`vj`. Condition (iii) is stated with the number of children `numChildren τ v` as `k_v(τ)`. The
restriction `p ≥ 2` is a hypothesis of the theorems, not of the predicate. -/
def IsPTree (p : ℕ) (τ : Finset (List ℕ+)) : Prop :=
  [] ∈ τ ∧ (∀ (v : List ℕ+) (j : ℕ+), v ++ [j] ∈ τ → v ∈ τ) ∧
  (∀ v ∈ τ, ∀ j : ℕ+, v ++ [j] ∈ τ ↔ (j : ℕ) ≤ numChildren τ v) ∧
  ∀ v ∈ τ, Odd v.length → numChildren τ v = p - 1

end LeGallBrownianMap


