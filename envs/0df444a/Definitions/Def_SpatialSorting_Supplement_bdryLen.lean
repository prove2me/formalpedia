-- Prove2me | Definitions.Def_SpatialSorting_Supplement_bdryLen
-- name    : SpatialSorting_Supplement_bdryLen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:35:24.423766+00:00
-- url     : https://prove2.me/theorems/b07d8843-c32e-4567-83aa-e4b421d30784
-- title:
--   Boundary length $|\partial_E R|$ of a region $R\subseteq I_L$ in the induced free-site graph
-- statement:
--   Let $G_L$ be the graph induced by the triangular lattice on the free sites $I_L=\{2,\dots,L-3\}^2$ of the rhombus $D_L$. For a set of sites $R\subseteq I_L$, its **edge boundary** is
--   $$
--   \partial_E R=\{\{u,v\}\in E(G_L) : u\in R,\ v\in I_L\setminus R\},
--   $$
--   and its **boundary length** is $|\partial_E R|$. Edges from $R$ to the fixed collar $B_L=D_L\setminus I_L$ are not counted: the boundary length is measured in the induced free-site graph only.
--
--   This is the perimeter notion of Definition 1.6: the low-perimeter regions tested by the Integrated event are those with $|\partial_E R|\le c\sqrt{|R|}$.
--
--   **Formalization Note** Every edge of $\partial_E R$ has exactly one endpoint in $R$, so the count of ordered pairs $(u,v)$ with $u\in R$, $v\in I_L\setminus R$, $u\sim v$ counts each boundary edge once. The function is defined for every finite set of sites and is used only for $R\subseteq I_L$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (boundary length, before Definition 1.6), p. 9 (PDF p. 10); edge boundary ∂_E R, §8, p. 46 (PDF p. 47)

import Mathlib
import Definitions.Def_SpatialSorting_tri
import Definitions.Def_SpatialSorting_I
open Classical Filter Topology

namespace SpatialSorting.Supplement

/-- The boundary length `|∂_E R|` of a region `R ⊆ I_L`: the number of edges `{u, v}` of the graph
`G_L` induced by the triangular lattice on the free sites `I_L` with `u ∈ R` and `v ∈ I_L \ R`.
Edges from `R` to the fixed collar `B_L = D_L \ I_L` are not counted.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (boundary length before Definition 1.6), p. 9 (PDF p. 10); `∂_E R`, §8, p. 46 (PDF p. 47).

Formalization Note: each edge of `∂_E R` has exactly one endpoint in `R`, so counting ordered pairs
`(u, v)` with `u ∈ R`, `v ∈ I_L \ R`, `u ~ v` counts every boundary edge exactly once. `R` is any
finite set of sites; the definition is used only for `R ⊆ I_L`. -/
noncomputable def bdryLen (L : ℕ) (R : Finset (ℤ × ℤ)) : ℕ :=
  ((R ×ˢ (I L \ R)).filter (fun p => tri.Adj p.1 p.2)).card

end SpatialSorting.Supplement


