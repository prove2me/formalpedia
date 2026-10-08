-- Prove2me | Definitions.Def_ExplicitExpanders_Attach_attachMatrix
-- name    : ExplicitExpanders_Attach_attachMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T06:13:47.08683+00:00
-- url     : https://prove2.me/theorems/92f9a057-0682-404b-9cbf-8576a979c8cc
-- title:
--   The graph $G$ of Theorem 1.2: new vertices attached to disjoint sets, loops elsewhere, $A_G=A_H+A_R+A_L$ (Section 2.4)
-- statement:
--   This file defines the graph $G$ built in the proof of Theorem 1.2, through its adjacency matrix and the three summands of equation (2).
--
--   Let $H$ be a simple graph on a finite vertex set $V$, let $r\ge 0$, and let $R=\{u_1,\dots,u_r\}$ be a set of $r$ new vertices (in Lean, $R=\mathrm{Fin}\,r$). For each $i$ let $W_i\subseteq V$ be a set of old vertices; the new vertex $u_i$ will be joined to every vertex of $W_i$. Write
--   $$W=\bigcup_{i} W_i,\qquad L=V\setminus W .$$
--   The vertex set of $G$ is $U=V\cup R$ (the disjoint union $V\oplus R$), and its adjacency matrix is
--   $$A_G=A_H+A_R+A_L,$$
--   where
--
--   1. $A_H$ is the adjacency matrix of $H$, extended by zero rows and columns on $R$ (the new vertices are isolated in it);
--   2. $A_R$ is the adjacency matrix of the graph $(U,E_R)$ whose edges join $u_i$ to each vertex of $W_i$: its $(v,u_i)$ and $(u_i,v)$ entries are $1$ if $v\in W_i$ and $0$ otherwise, and its other entries are $0$;
--   3. $A_L$ is diagonal, with entry $1$ at every vertex of $L$ and $0$ elsewhere: one loop at each vertex of $L$, counted once in the degree, as in the paper's convention "a loop adds one to the degree".
--
--   In the paper, $H$ is the $(p+1)$-regular Ramanujan graph of Lubotzky, Phillips and Sarnak on $SL(2,\mathbb F_q)$, the sets $W_i$ are consecutive blocks of $p+2$ vertices in a fixed numbering, and $G$ is then $(p+2)$-regular. The definition here allows any sets $W_i$; the theorems of this mission assume they are pairwise disjoint of size $p+2$, which is all the spectral argument uses (the overview on p. 3 speaks of "arbitrary disjoint sets of neighbors").
--
--   **Formalization Note** The file also defines the auxiliary sets `attachedSet W` $=W$ and `loopSet W` $=L$, and the $V\times R$ incidence matrix of the stars. The loops-to-matching variant for even $n$ (p. 8) is not modelled.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 8, Section 2.4 (construction of G; W, L, E_R; A_G = A_H + A_R + A_L, eq. (2)); p. 3 (loop convention)

import Mathlib

namespace ExplicitExpanders.Attach

open Matrix

/-- The set `W = ⋃ᵢ W i ⊆ V` of old vertices that receive a new neighbour
(arXiv:2003.11673v1, §2.4, p. 8). -/
def attachedSet {V : Type*} [DecidableEq V] {r : ℕ} (W : Fin r → Finset V) : Finset V :=
  Finset.univ.biUnion W

/-- The set `L = V ∖ W` of old vertices that receive a loop (§2.4, p. 8). -/
def loopSet {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} (W : Fin r → Finset V) :
    Finset V :=
  Finset.univ \ attachedSet W

/-- `A_H`: the adjacency matrix of `H` on `V`, extended by zero to the vertex set `V ⊕ Fin r`
of `G` (the new vertices of `R = Fin r` are isolated in it) (§2.4, p. 8). -/
def matH {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (r : ℕ) : Matrix (V ⊕ Fin r) (V ⊕ Fin r) ℝ :=
  Matrix.fromBlocks (H.adjMatrix ℝ) 0 0 0

/-- The `V × R` incidence matrix of the stars: entry `(v, i)` is `1` if `v ∈ W i`
(the new vertex `uᵢ` is joined to `v`) and `0` otherwise. -/
def incidence {V : Type*} {r : ℕ} [DecidableEq V] (W : Fin r → Finset V) :
    Matrix V (Fin r) ℝ :=
  Matrix.of fun v i => if v ∈ W i then 1 else 0

/-- `A_R`: the adjacency matrix of the graph `(U, E_R)` on `U = V ⊕ Fin r`, whose edges join
each new vertex `uᵢ` to the vertices of `W i` (§2.4, p. 8). -/
def matR {V : Type*} [DecidableEq V] {r : ℕ} (W : Fin r → Finset V) :
    Matrix (V ⊕ Fin r) (V ⊕ Fin r) ℝ :=
  Matrix.fromBlocks 0 (incidence W) (incidence W)ᵀ 0

/-- `A_L`: the loops on the vertices of `L`, one per vertex, each a diagonal entry `1`
("a loop adds one to the degree", p. 3) (§2.4, p. 8). -/
def matL {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} (W : Fin r → Finset V) :
    Matrix (V ⊕ Fin r) (V ⊕ Fin r) ℝ :=
  Matrix.fromBlocks (Matrix.diagonal fun v => if v ∈ loopSet W then (1 : ℝ) else 0) 0 0 0

/-- The adjacency matrix of the graph `G` of the proof of Theorem 1.2: `H` on `V`, new
vertices `Fin r` with `uᵢ` joined to `W i`, and a loop at every vertex of `L = V ∖ ⋃ᵢ W i`;
`A_G = A_H + A_R + A_L` (§2.4, p. 8). -/
def matG {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    {r : ℕ} (W : Fin r → Finset V) : Matrix (V ⊕ Fin r) (V ⊕ Fin r) ℝ :=
  matH H r + matR W + matL W

end ExplicitExpanders.Attach


