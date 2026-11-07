-- Prove2me | Definitions.Def_IIDMatchHard_Reduction
-- name    : IIDMatchHard_Reduction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:06:26.943336+00:00
-- url     : https://prove2.me/theorems/a4ee75f3-a915-40d6-b83f-d68642f96d3e
-- title:
--   The rational instance $I(\tilde G,c/B)$ built from a graph
-- statement:
--   Let $G$ be a graph on $\{0,\dots,N-1\}$, let $c>0$ be rational and let $B\ge1$ be an integer. Put $\lambda=c/B$. The input $I(\tilde G,\lambda)$ describes the instance of §3.1 built on the blow-up $\tilde G$, with explicit enumerations:
--
--   1. vertex $(a,i)$ of $\tilde G$ is $x=aB+i\in\{0,\dots,NB-1\}$, and its offline vertices are $x^+=2x$ and $x^-=2x+1$;
--   2. the edges $x<y$ of $\tilde G$ are listed lexicographically. With $E$ the number of edges, type $x<NB$ is the vertex type $x$, and type $NB+2j+b$ is the edge type $e_j^{+}$ ($b=0$) or $e_j^{-}$ ($b=1$) of the $j$-th edge;
--   3. vertex types have probability $1/R$ and edge types $\lambda/R$, where $R=NB+2E\lambda$, and there are $T=\lceil R\rceil$ online vertices.
--
--   This is the instance the reduction of App. B.9 queries.
--
--   **Formalization Note** The map is total. For $NB=0$ it produces the input with no types, which is not valid; the reduction handles small graphs by brute force.
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), §3.1, p.5 (PDF p.6); proof of Theorem 3.1, App. B.9, p.23 (PDF p.24)

import Definitions.Def_IIDMatchHard_Inst
import Definitions.Def_NSWApxHard_Reduction_CubicVC

set_option autoImplicit false

namespace IIDMatchHard

open NSWApxHard.Reduction

open Classical in
/-- The edges `x < y` of the blow-up of `H` with `B` copies, on the flattened vertex set
`Fin (N·B)` (vertex `(a, i)` of `Fin N × Fin B` is `finProdFinEquiv (a, i) = a·B + i`), listed in
lexicographic order. -/
noncomputable def blowEdges (B : ℕ) (H : GraphInput) : List (Fin (H.N * B) × Fin (H.N * B)) :=
  (List.finRange (H.N * B)).flatMap fun x =>
    ((List.finRange (H.N * B)).filter fun y =>
      decide (x < y ∧ H.G.Adj (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm y).1)).map
      fun y => (x, y)

/-- The rational instance **`I(G̃, λ)` with `λ = c/B`** built from the graph `H` on `Fin N` and its
blow-up `G̃` with `B` copies (the instance queried in the proof of Theorem 3.1, App. B.9, p.23
(PDF p.24)), with explicit enumerations:

1. offline vertices `Fin (2·N·B)`: vertex `x` of `G̃` gives `x⁺ = 2x` and `x⁻ = 2x + 1`;
2. types `Fin (N·B + 2E)`, `E` the number of edges of `G̃`: type `x < N·B` is the vertex type `x`,
   with neighbors `(2x, 2x + 1)`; type `N·B + 2j + b` is the edge type `e_j^{s}` of the `j`-th edge
   `e_j = (x, y)` of `blowEdges`, with `s = +` for `b = 0` and `s = −` for `b = 1`, and neighbors
   `(2x + b, 2y + b)`;
3. probabilities `1/R` for a vertex type and `λ/R` for an edge type, `R = N·B + 2Eλ`;
4. `T = ⌈R⌉` online vertices.

Teng, Yang, *Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026,
sha256 f0193d92…), §3.1, p.5 and App. B.9, p.23.

**Formalization Note.** The map is total: for `N·B = 0` it gives the instance with no types (which
is not `Inst.Valid`). -/
noncomputable def redInst (c : ℚ) (B : ℕ) (H : GraphInput) : Inst where
  nOff := 2 * (H.N * B)
  nTy := H.N * B + 2 * (blowEdges B H).length
  nbr t :=
    if h : t.val < H.N * B then
      (⟨2 * t.val, by omega⟩, ⟨2 * t.val + 1, by omega⟩)
    else
      have hj : (t.val - H.N * B) / 2 < (blowEdges B H).length := by
        have := t.isLt; omega
      have hb : (t.val - H.N * B) % 2 < 2 := Nat.mod_lt _ (by norm_num)
      ((⟨2 * ((blowEdges B H).get ⟨_, hj⟩).1.val + (t.val - H.N * B) % 2,
          by have := ((blowEdges B H).get ⟨_, hj⟩).1.isLt; omega⟩ : Fin (2 * (H.N * B))),
        (⟨2 * ((blowEdges B H).get ⟨_, hj⟩).2.val + (t.val - H.N * B) % 2,
          by have := ((blowEdges B H).get ⟨_, hj⟩).2.isLt; omega⟩ : Fin (2 * (H.N * B))))
  prob t :=
    if t.val < H.N * B then 1 / ((H.N * B : ℚ) + 2 * (blowEdges B H).length * (c / B))
    else (c / B) / ((H.N * B : ℚ) + 2 * (blowEdges B H).length * (c / B))
  T := ⌈(H.N * B : ℚ) + 2 * (blowEdges B H).length * (c / B)⌉₊

end IIDMatchHard


