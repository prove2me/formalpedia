-- Prove2me | Definitions.Def_FASTournament_InP
-- name    : FASTournament_InP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:59.013265+00:00
-- url     : https://prove2.me/theorems/5791de62-0996-4325-866d-aa6662f1dac6
-- title:
--   The class $\mathcal P$ (Theorem 2.7, Figure 7)
-- statement:
--   $\mathcal P$ is the class of all strong tournaments $T$ with the global structure of Figure 7: there are $m\ge 1$, distinct **join vertices** $v_1,\dots,v_m$, **vertical blocks** $A_1,\dots,A_m$ and **horizontal blocks** $B_1,\dots,B_{m-1}$, with $v_i\in A_i$ and $v_i,v_{i+1}\in B_i$, such that the join vertices, the sets $A_i\setminus v_i$ and the sets $B_i\setminus\{v_i,v_{i+1}\}$ partition $V$, and:
--
--   1. each $T[A_i]$ is in $\mathcal Q$ with center $v_i$ and building blocks $A_{i,1},\dots,A_{i,n_i}$ from left to right ($n_i\ge 0$); arcs between $v_i$ and $A_i\setminus v_i$ are arbitrary;
--   2. each $T[B_i]$ has one of three shapes: $B_i=\{v_i,v_{i+1}\}$ with the arc $v_{i+1}v_i$; or $B_i=\{v_i,z,v_{i+1}\}$ with arcs $v_{i+1}v_i$, $v_{i+1}z$, $zv_i$; or $B_i=\{v_i,x,y,v_{i+1}\}$ with arcs $xv_i$, $yv_i$, $v_iv_{i+1}$, $v_{i+1}x$, $v_{i+1}y$, $xy$;
--   3. all other arcs are directed from "left" to "right" in the order $A_1,\ B_1\setminus\{v_1,v_2\},\ A_2,\ \dots,\ B_{m-1}\setminus\{v_{m-1},v_m\},\ A_m$;
--   4. $v_1$ has an out-neighbor in the leftmost building block of $A_1$, and $v_m$ has an in-neighbor in the rightmost building block of $A_m$.
--
--   **Formalization Note** The blocks are encoded by a group index $g:V\to\{0,\dots,2m-2\}$ with $A_i=g^{-1}(2i)$ and $B_i=g^{-1}(2i+1)\cup\{v_i,v_{i+1}\}$ (0-based $i$), and by a position $\mathrm{pos}(x)\in\{1,\dots,n_i\}$ of each vertex of $A_i\setminus v_i$ in its building block. "All other arcs" means pairs of vertices lying in no common block; since two blocks share at most one vertex, each pair is governed by at most one block. Item 4 is read existentially: the named building blocks exist, so $n_1\ge1$ and $n_m\ge1$. The data are existentially quantified.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Theorem 2.7, Figure 7 and the paragraph after it, p.8

import Mathlib
import Definitions.Def_FASTournament_IsTournament
import Definitions.Def_FASTournament_IsStrong
import Definitions.Def_FASTournament_IsSingletonOrTriangle

namespace FASTournament

/-- **The class `𝒫` (Theorem 2.7 and Figure 7).**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Theorem 2.7, Figure 7 and the paragraph after it, p.8: "where m ≥ 1 (undirected/dotted
edges in the following can be directed arbitrarily), and all other arcs (that are not drawn) are
directed from “left” to “right”. Furthermore, v1 has an out-neighbor in the leftmost building
block of A1, and vm has an in-neighbor in the rightmost building block of Am. … each Ai contains
vi and each Bi contains both vi and vi+1. Let P denote the class of all strong tournaments T
described in the above theorem."

`T` is a strong tournament and there are `m ≥ 1`, distinct join vertices `v 0, …, v (m-1)` (the
paper's `v₁, …, v_m`), vertical blocks `A₀, …, A_{m-1}` and horizontal blocks
`B₀, …, B_{m-2}`, encoded by a group index `g : V → {0, …, 2m-2}`:
`Aᵢ = {x | g x = 2i}` (it contains `v i`), and `Bᵢ = {x | g x = 2i+1} ∪ {v i, v (i+1)}`.
1. Each `T[Aᵢ]` is in `𝒬` with center `v i`: its other vertices carry a position
   `pos x ∈ {1, …, n i}`, each building block `{x ∈ Aᵢ ∖ v i | pos x = j}` is a singleton or a
   triangle, and arcs between building blocks go from lower to higher position. Arcs between
   `v i` and `Aᵢ ∖ v i` are arbitrary (the dotted edges).
2. Each `T[Bᵢ]` is one of the three shapes of Figure 7: `Bᵢ = {vᵢ, vᵢ₊₁}` with `vᵢ₊₁ → vᵢ`;
   or `Bᵢ = {vᵢ, z, vᵢ₊₁}` with `vᵢ₊₁ → vᵢ`, `vᵢ₊₁ → z`, `z → vᵢ`; or `Bᵢ = {vᵢ, x, y, vᵢ₊₁}` with
   `x → vᵢ`, `y → vᵢ`, `vᵢ → vᵢ₊₁`, `vᵢ₊₁ → x`, `vᵢ₊₁ → y`, `x → y`.
3. Left to right: if two vertices lie in no common block and `g x < g y`, then `x → y`.
4. `v 0` has an out-neighbour in the leftmost building block of `A₀` (position `1`), and
   `v (m-1)` has an in-neighbour in the rightmost building block of `A_{m-1}` (position
   `n (m-1)`).

**Formalization Note.** The order of the groups is `A₀, B₀°, A₁, B₁°, …, A_{m-1}`, where
`Bᵢ° = Bᵢ ∖ {vᵢ, vᵢ₊₁}`; two distinct blocks share at most one vertex, so every pair of vertices
is governed by at most one block. Item 4 is read existentially: the building blocks named exist
(so `n 0 ≥ 1` and `n (m-1) ≥ 1`). Indices are 0-based (`v i` is the paper's `v_{i+1}`). -/
def InP {V : Type*} (T : Digraph V) : Prop :=
  IsTournament T ∧ IsStrong T ∧
  ∃ (m : ℕ) (v : ℕ → V) (g : V → ℕ) (n : ℕ → ℕ) (pos : V → ℕ),
    1 ≤ m ∧ Set.InjOn v {i | i < m} ∧ (∀ x, g x + 1 < 2 * m) ∧ (∀ i < m, g (v i) = 2 * i) ∧
    -- vertical blocks: `T[Aᵢ] ∈ 𝒬` with center `v i` and building blocks `1, …, n i`
    (∀ i < m, ∀ x, g x = 2 * i → x ≠ v i → 1 ≤ pos x ∧ pos x ≤ n i) ∧
    (∀ i < m, ∀ j, 1 ≤ j → j ≤ n i →
      IsSingletonOrTriangle T {x | g x = 2 * i ∧ x ≠ v i ∧ pos x = j}) ∧
    (∀ i < m, ∀ x y, g x = 2 * i → g y = 2 * i → x ≠ v i → y ≠ v i → pos x < pos y →
      T.Adj x y) ∧
    -- horizontal blocks: the three shapes of Figure 7
    (∀ i, i + 1 < m →
      ((∀ x, g x ≠ 2 * i + 1) ∧ T.Adj (v (i + 1)) (v i)) ∨
      (∃ z, (∀ x, g x = 2 * i + 1 ↔ x = z) ∧
        T.Adj (v (i + 1)) (v i) ∧ T.Adj (v (i + 1)) z ∧ T.Adj z (v i)) ∨
      (∃ x y, x ≠ y ∧ (∀ u, g u = 2 * i + 1 ↔ u = x ∨ u = y) ∧
        T.Adj x (v i) ∧ T.Adj y (v i) ∧ T.Adj (v i) (v (i + 1)) ∧
        T.Adj (v (i + 1)) x ∧ T.Adj (v (i + 1)) y ∧ T.Adj x y)) ∧
    -- all other arcs go from left to right
    (∀ x y, g x < g y →
      ¬ (∃ i < m, g x = 2 * i ∧ g y = 2 * i) →
      ¬ (∃ i, i + 1 < m ∧ (g x = 2 * i + 1 ∨ x = v i ∨ x = v (i + 1)) ∧
          (g y = 2 * i + 1 ∨ y = v i ∨ y = v (i + 1))) →
      T.Adj x y) ∧
    -- the two end conditions
    (∃ x, g x = 0 ∧ x ≠ v 0 ∧ pos x = 1 ∧ T.Adj (v 0) x) ∧
    (∃ x, g x = 2 * (m - 1) ∧ x ≠ v (m - 1) ∧ pos x = n (m - 1) ∧ T.Adj x (v (m - 1)))

end FASTournament


