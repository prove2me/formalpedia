-- Prove2me | Definitions.Def_LeGallBrownianMap_numChildren
-- name    : LeGallBrownianMap_numChildren
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:11.284325+00:00
-- url     : https://prove2.me/theorems/3d0468c2-5f77-4727-a603-74861818a97e
-- title:
--   Number of children $k_v(\tau)$ of a vertex of a plane tree
-- statement:
--   Vertices of plane trees are finite sequences of positive integers (Ulam–Harris words), the root being the empty sequence $\varnothing$; the children of $v=(u_1,\dots,u_k)$ are the sequences $vj=(u_1,\dots,u_k,j)$. For a finite set $\tau$ of words and a word $v$, $k_v(\tau)$ is the number of children of $v$ that lie in $\tau$.
--
--   **Formalization Note** Words are lists of positive integers; $vj$ is `v ++ [j]`.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.1, p.8

import Mathlib

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.1, p.8:
plane trees are finite subsets of `U = ⋃_n ℕ^n`, finite sequences of positive integers, and
"for every v = (u_1, ..., u_k) ∈ τ there exists an integer k_v(τ) ≥ 0 such that, for every j ∈ ℕ,
the vertex vj := (u_1, ..., u_k, j) belongs to τ if and only if 1 ≤ j ≤ k_v(τ) [the vertices of the
form vj with 1 ≤ j ≤ k_v(τ) are called the children of v]."

`numChildren τ v` is the number of children of `v` in `τ`: the elements of `τ` of the form
`v ++ [j]`. For a plane tree it is `k_v(τ)`.

**Formalization Note.** Vertices are lists `List ℕ+` (Ulam–Harris words); `v ++ [j]` is the
paper's `vj`. A list `u` is of that form iff `u` is one longer than `v` and starts with `v`. -/
def numChildren (τ : Finset (List ℕ+)) (v : List ℕ+) : ℕ :=
  (τ.filter (fun u => u.length = v.length + 1 ∧ u.take v.length = v)).card

end LeGallBrownianMap


