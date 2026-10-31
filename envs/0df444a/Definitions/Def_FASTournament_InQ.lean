-- Prove2me | Definitions.Def_FASTournament_InQ
-- name    : FASTournament_InQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:49.943686+00:00
-- url     : https://prove2.me/theorems/65e86832-ae0e-48c9-b460-cf1e6bf4a877
-- title:
--   The class $\mathcal Q$
-- statement:
--   $\mathcal Q$ consists of all tournaments $G$ whose vertex set can be partitioned into $U_0,U_1,\dots,U_k$ for some integer $k\ge 0$, such that
--
--   1. $|U_0|=1$;
--   2. $G[U_i]$ is either a singleton or a triangle for $1\le i\le k$; and
--   3. the arcs between $U_i$ and $U_j$ are all directed to $U_j$ for $1\le i<j\le k$.
--
--   The vertex $v$ of $U_0$ is the **center**, and $H_i=G[U_i\cup\{v\}]$ are the **building blocks**, $H_1$ the leftmost and $H_k$ the rightmost. Arcs between the center and the $U_i$ are arbitrary.
--
--   **Formalization Note** The partition is a function $\mathrm{blk}:V\to\mathbb N$ with $U_j=\mathrm{blk}^{-1}(j)$, $U_0=\{c\}$ and $\mathrm{blk}\le k$.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.8

import Mathlib
import Definitions.Def_FASTournament_IsTournament
import Definitions.Def_FASTournament_IsSingletonOrTriangle

namespace FASTournament

/-- **The class `𝒬`.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.8: "Let Q consist of all tournaments G whose vertex set can be partitioned into
U0, U1, . . . , Uk for some integer k ≥ 0, such that |U0| = 1, G[Ui] is either a singleton or a
triangle for 1 ≤ i ≤ k, and the arcs between Ui and Uj are all directed to Uj for
1 ≤ i < j ≤ k. Let v be the vertex in U0. We call v the center of G".

The partition is given by `blk : V → ℕ` with `Uᵢ = blk⁻¹(i)`: `U₀ = {c}` (the center), every
vertex has `blk ≤ k`, each `G[Uⱼ]`, `1 ≤ j ≤ k`, is a singleton or a triangle, and every vertex
of `Uᵢ` sends an arc to every vertex of `Uⱼ` for `1 ≤ i < j`. Arcs between the center and the
`Uᵢ` are unconstrained.

**Formalization Note.** The data `c, k, blk` are existentially quantified. -/
def InQ {V : Type*} (G : Digraph V) : Prop :=
  IsTournament G ∧ ∃ (c : V) (k : ℕ) (blk : V → ℕ),
    (∀ x, blk x = 0 ↔ x = c) ∧ (∀ x, blk x ≤ k) ∧
    (∀ j, 1 ≤ j → j ≤ k → IsSingletonOrTriangle G {x | blk x = j}) ∧
    ∀ x y, 1 ≤ blk x → blk x < blk y → G.Adj x y

end FASTournament


