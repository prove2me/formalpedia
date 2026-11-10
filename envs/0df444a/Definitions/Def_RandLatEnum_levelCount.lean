-- Prove2me | Definitions.Def_RandLatEnum_levelCount
-- name    : RandLatEnum_levelCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:00.81441+00:00
-- url     : https://prove2.me/theorems/6c68ce4e-9d26-4f6f-97b5-931c0eaf382c
-- title:
--   Nodes at one level of the enumeration tree, $N_d(B,R)$
-- statement:
--   Let $B=(b_1,\dots,b_n)$ be an ordered basis of a lattice $L$, and let $\pi_i$ be the orthogonal projection onto $\mathrm{span}(b_1,\dots,b_{i-1})^\perp$. At depth $d$ ($1\le d\le n$) full enumeration has fixed the coefficients of the last $d$ basis vectors, and the nodes at that depth are the points of the projected lattice $L_{B,d}=\pi_{n-d+1}(L)$ in the ball of radius $R$:
--   $$
--   N_d(B,R)=\#\bigl(\pi_{n-d+1}(L)\cap B_d(R)\bigr).
--   $$
--   The zero vector is counted (one node per coefficient tuple). For $d=n$ the projection is the identity and $N_n(B,R)=\#(L\cap B(R))$ counts the leaves.
--
--   **Formalization Note** Indexed by the 0-based projection index $j=n-d\in\{0,\dots,n-1\}$: `levelCount b j R` counts `projLattice b j` $=\pi_{j+1}(L)$ inside the closed ball of radius $R$. The count is `Set.ncard`; it is finite for a lattice (an infinite set would count $0$, which only lowers a tree size).
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §3.1, (3.1), p.17; (2.2), p.14

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice

namespace RandLatEnum

/-- The number of enumeration-tree nodes at one level, `N_d(B, R) = #(L_{B,d} ∩ B_d(R))`
(Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §3.1, (3.1), p.17), with `L_{B,d} = π_{n−d+1}(L)` ((2.2), p.14).

**Formalization Note.** Indexed by the 0-based projection index `j = n − d`: `levelCount b j R`
counts the points of `projLattice b j = π_{j+1}(L)` (projection orthogonal to `b_0, …, b_{j−1}`)
in the **closed** ball of radius `R`, the zero vector included (one node per coefficient tuple,
p.17). `j = 0` is the lattice itself (the leaves, `d = n`). The count is `Set.ncard`; it is finite
for every lattice, and an infinite set would count `0`, which only lowers a tree size. -/
noncomputable def levelCount {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (j : Fin m)
    (R : ℝ) : ℕ :=
  (KannanLattice.Core.projLattice b j ∩ Metric.closedBall 0 R).ncard

end RandLatEnum


