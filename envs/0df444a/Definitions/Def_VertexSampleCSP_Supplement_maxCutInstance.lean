-- Prove2me | Definitions.Def_VertexSampleCSP_Supplement_maxCutInstance
-- name    : VertexSampleCSP_Supplement_maxCutInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:58:14.132227+00:00
-- url     : https://prove2.me/theorems/2a533484-3d85-48be-a679-71dc9c258084
-- title:
--   Max-Cut of an $r$-uniform hypergraph as an instance over $[2]$
-- statement:
--   Let $E$ be a family of subsets (edges) of a finite vertex set $V$. The **Max-Cut instance** of $E$ is the instance of arity $r$ over the alphabet $[2]$ whose table on a set $e$ is
--
--   $$f_e(a)=\begin{cases}1,& e\in E\text{ and } a \text{ is not constant on } e,\\ 0,&\text{otherwise.}\end{cases}$$
--
--   An edge is cut by a 2-colouring unless all its vertices receive the same colour, so the optimum $\mathrm{OPT}$ of this instance is the largest number of cut edges, the Max-Cut of the hypergraph, and its subinstance on a set $S$ is the Max-Cut instance of the edges contained in $S$.
--
--   These are the hard instances of both lower bounds of the paper (Theorems E.1 and E.4).
--
--   **Formalization Note** The two sides are the labels of `Fin 2`. Only tables on $r$-subsets are read by the published instance model, so the theorems that use this definition assume that every edge has exactly $r$ vertices; for $r\ge 2$ the number of edges is then the number of nonzero tables.
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), §1.1, p.2 (PDF p.4); Appendix A, "Instances", p.13 (PDF p.15)

import Mathlib
import Definitions.Def_VertexSampleCSP_Instance

namespace VertexSampleCSP.Supplement

open Classical in
/-- **Max-Cut of an `r`-uniform hypergraph as an instance over `[2]`.** Chang, *Optimal Vertex
Sampling for Constraint Satisfaction Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…),
§1.1, p.2 (PDF p.4): "Max-Cut of r-uniform hypergraphs, in which an edge is cut unless all its
vertices lie on the same side"; Appendix A, "Instances", p.13 (PDF p.15): "Max-Cut of an r-uniform
hypergraph has fe(a) = 1 unless all entries of a are equal."

For a family `E` of subsets of `V` (the edges), `maxCutInstance r E` is the instance of arity `r`
over `[2]` whose table on a set `e` is `1` at a labelling `a` of `e` exactly when `e` is an edge and
`a` is not constant, and `0` otherwise (in particular the table of a non-edge is zero). Its optimum
`OPT (maxCutInstance r E)` is the largest number of edges that are not monochromatic under a
2-colouring of `V`, the hypergraph Max-Cut.

**Formalization Note.** The two sides are the labels `0, 1 : Fin 2`. The instance reads only the
tables on `r`-subsets, so the statements that use it assume that every edge has exactly `r`
vertices (`r`-uniformity). For `r ≥ 2` the table of an edge is nonzero, so the number of
constraints of the instance is the number of edges `E.card`. -/
noncomputable def maxCutInstance {V : Type*} [Fintype V] [DecidableEq V] (r : ℕ)
    (E : Finset (Finset V)) : Instance V r 2 where
  f e a := if e ∈ E ∧ ¬ (∀ x y, a x = a y) then 1 else 0

end VertexSampleCSP.Supplement


