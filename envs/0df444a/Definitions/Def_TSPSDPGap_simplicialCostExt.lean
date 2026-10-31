-- Prove2me | Definitions.Def_TSPSDPGap_simplicialCostExt
-- name    : TSPSDPGap_simplicialCostExt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:27.192049+00:00
-- url     : https://prove2.me/theorems/ca27233b-7b9f-41b4-b26d-c51791c0d1a4
-- title:
--   Simplicial instance on $n+1$ cities with an extra vertex in group 1
-- statement:
--   The instance of the proof of Theorem 4.1 has $n+1$ vertices in $g$ groups: groups $2,\dots,g$ have $n/g$ vertices each and group $1$ has $n/g+1$. Costs are $0$ inside a group and $1$ between groups. Concretely, a distinguished vertex $s$ is the extra vertex of group $1$, and the other $n$ vertices, listed in increasing order, are split into consecutive groups of $n/g$ as in the $n$-city simplicial instance. Deleting $s$ leaves the $n$-city instance $(J_g-I_g)\otimes J_{n/g}$.
--
--   **Formalization Note** Vertices are `Fin (n+1)`; for $s=0$ (the paper's vertex $1$) this is the paper's labelling. The group of $s$ is $0$ and the group of the $i$-th remaining vertex is $\lfloor i/(n/g)\rfloor$.
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, proof of Theorem 4.1, p.27; costs p.14

import Mathlib

namespace TSPSDPGap

/-- **The simplicial instance on `n + 1` cities with one extra vertex in group 1.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, proof of Theorem 4.1, p.27: "consider an instance of the TSP on n + 1
vertices with g = 2z groups of vertices. Specifically, let groups 2, ..., g be equally sized,
each of size n/g ∈ ℕ, and let group 1 have one extra vertex, so that group one is of size
n/g + 1", with the costs of p.14 (0 inside a group, 1 between groups).

The extra vertex is `s`; the remaining `n` vertices, listed increasingly, are split into groups
of `n/g` consecutive vertices exactly as in `simplicialCost g n`, and `s` joins the first group.

**Formalization Note.** Vertices are `Fin (n + 1)` (0-based). The group of the vertex
`s.succAbove i` is `⌊i / (n/g)⌋` and the group of `s` is `0` (`Fin.insertNth`). For `s = 0`
this is the paper's labelling (vertex 1 is the extra vertex and `D[{2, …, n+1}]` is
`(J_g − I_g) ⊗ J_{n/g}`); for any `s`, deleting `s` gives `simplicialCost g n`. -/
def simplicialCostExt (g n : ℕ) (s : Fin (n + 1)) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  let grp : Fin (n + 1) → ℕ := Fin.insertNth (α := fun _ => ℕ) s 0 (fun i : Fin n => (i : ℕ) / (n / g))
  Matrix.of fun u v => if grp u = grp v then 0 else 1

end TSPSDPGap


