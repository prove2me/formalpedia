-- Prove2me | Definitions.Def_GyoriLovasz_Instance
-- name    : GyoriLovasz_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:25.516201+00:00
-- url     : https://prove2.me/theorems/a278449e-97ca-4640-97dd-cd283cbc6f29
-- title:
--   Input of the algorithm: vertices, edge list, terminals with capacities
-- statement:
--   An **input** of the algorithm of Theorems 1 and 2 consists of a number $n$ (the vertices are $0,\dots,n-1$), a list of directed edges $(x,y)$, and a list whose $i$-th entry is $(t_i,c_i)$, the terminal $t_i$ with its capacity $c_i$. It is **well formed** if all endpoints and terminals are below $n$ and the terminals are distinct. The input determines the directed graph on $\{0,\dots,n-1\}$, the terminal set $T$, and the capacity map $t_i\mapsto c_i$.
--
--   **Formalization Note** Repeated entries of the edge list denote one edge. The graph keeps only edges with endpoints below $n$, which on a well-formed input is every edge.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Theorem 1, p.5; §2, p.14

import Mathlib
import Definitions.Def_GyoriLovasz_DG

namespace GyoriLovasz

/-- **An input of the algorithm of Theorems 1 and 2.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Theorem 1, p.5.
`n` is the number of vertices, which are `0, …, n − 1`; `edges` lists the directed edges; entry `i` of `terms` is
`(t_i, c_i)`, the terminal `t_i` with its capacity. -/
structure Instance where
  n : ℕ
  edges : List (ℕ × ℕ)
  terms : List (ℕ × ℕ)

namespace Instance

/-- Well-formed input: all endpoints and terminals are vertices, and the terminals are distinct ("a set of distinct
terminals", Theorem 1, p.5). Repeated entries of `edges` denote one edge. -/
def WellFormed (I : Instance) : Prop :=
  (∀ e ∈ I.edges, e.1 < I.n ∧ e.2 < I.n) ∧ (∀ x ∈ I.terms, x.1 < I.n) ∧ (I.terms.map Prod.fst).Nodup

/-- The directed graph of an input. The filter only makes `wf` hold; it is the identity on well-formed inputs. -/
def toDG (I : Instance) : DG ℕ where
  verts := Finset.range I.n
  arcs := I.edges.toFinset.filter fun e => e.1 < I.n ∧ e.2 < I.n
  wf := by
    intro a ha
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp ha
    exact ⟨Finset.mem_range.mpr h1, Finset.mem_range.mpr h2⟩

/-- The terminal set `T`. -/
def termSet (I : Instance) : Finset ℕ := (I.terms.map Prod.fst).toFinset

/-- The capacity of a terminal, read from `terms`; `0` off `T`, where it is never used. -/
def cap (I : Instance) (t : ℕ) : ℕ := (I.terms.lookup t).getD 0

end Instance

end GyoriLovasz


