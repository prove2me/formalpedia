-- Prove2me | Definitions.Def_SteurerHDX_vdeg
-- name    : SteurerHDX_vdeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:56.466188+00:00
-- url     : https://prove2.me/theorems/aeef6bfd-272b-4812-9d84-cc43f24c2f6c
-- title:
--   Weighted degree $D(x)=\sum_y W(x,y)$
-- statement:
--   A (weighted) graph on a finite set $\iota$ is given by its weighted adjacency matrix $W$ (symmetric, entrywise nonnegative; self-loops allowed). The **weighted degree** of $x$ is
--   $$D(x)=\sum_{y} W(x,y),$$
--   the diagonal entry of the degree matrix $D$.
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Section 2.1, p.3

import Mathlib

namespace SteurerHDX

/-- **Weighted degree.** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Section 2.1, p.3: "Given a (weighted) graph G = (V, E, w) with
(weighted) adjacency matrix A; let D be the diagonal matrix of vertex (weighted) degrees".

**Formalization Note.** A weighted graph on a finite type `ι` is its weighted adjacency matrix
`W` (symmetric and entrywise nonnegative in the theorems; self-loops allowed, as the down-up walk
needs). `vdeg W x = ∑_y W x y` is the diagonal entry D(x). -/
def vdeg {ι : Type*} [Fintype ι] (W : Matrix ι ι ℝ) (x : ι) : ℝ :=
  ∑ y, W x y

end SteurerHDX


