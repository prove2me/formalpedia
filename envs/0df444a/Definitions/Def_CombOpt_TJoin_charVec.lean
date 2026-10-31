-- Prove2me | Definitions.Def_CombOpt_TJoin_charVec
-- name    : CombOpt_TJoin_charVec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:03:45.492574+00:00
-- url     : https://prove2.me/theorems/4661f11e-5b2d-418d-9a19-9a4c9de2cabb
-- title:
--   Characteristic vector of a set
-- statement:
--   Let $E$ be a ground set (the edge set of a graph, or the ground set of a matroid) and let $J\subseteq E$ be a finite subset. The **characteristic vector** of $J$ is the vector $x\in\mathbb R^{E}$ with
--
--   $$x_e=\begin{cases}1, & e\in J,\\ 0, & e\notin J.\end{cases}$$
--
--   Characteristic vectors turn combinatorial objects (spanning trees, matchings, $T$-joins, independent sets of a matroid) into points of $\mathbb R^{E}$, so that a family of sets can be compared with a polyhedron; for $D\subseteq E$ the sum $x(D)=\sum_{e\in D}x_e$ then counts $|J\cap D|$.
--
--   **Formalization Note** The ground set is an arbitrary type with decidable equality, the set $J$ is a `Finset`, and the vector is real valued. The notation $x(D)$ is not part of this definition; statements that use it write the sum explicitly.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.4, p. 178 (PDF p. 186), the characteristic vector of a T-join before (5.32); first spelled out in §2.1, p. 14 (PDF p. 23); used for matroid elements in Chapter 8

import Mathlib

namespace CombOpt.TJoin

/-- **Characteristic vector of a set of edges.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.4, p. 178 (PDF p. 186): "the characteristic vector x of any T-join of G". The notion is first spelled out in §2.1, p. 14 (PDF p. 23): "x_u = 1 if u ∈ V(H), and x_u = 0 if u ∉ V(H)".

`charVec J e = 1` if `e ∈ J` and `0` otherwise.

**Formalization Note.** The ground set is an arbitrary type `E` (edges of a graph in Chapter 5,
elements of a matroid's ground set in Chapter 8); `J` is a `Finset`, and the vector is real valued,
`E → ℝ`, matching the book's vectors in `ℝ^E`. -/
def charVec {E : Type*} [DecidableEq E] (J : Finset E) : E → ℝ :=
  fun e => if e ∈ J then 1 else 0

end CombOpt.TJoin


