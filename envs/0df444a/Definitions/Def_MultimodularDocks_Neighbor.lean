-- Prove2me | Definitions.Def_MultimodularDocks_Neighbor
-- name    : MultimodularDocks_Neighbor
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:51.190418+00:00
-- url     : https://prove2.me/theorems/2f6eba3f-201b-4141-884e-bc6bda1b86f4
-- title:
--   The neighborhood $N(\vec d,\vec b)$
-- statement:
--   The **neighborhood** $N(\vec d,\vec b)$ consists of the allocations one dock-move away from $(\vec d,\vec b)$: the results of $o_{ij}$, $e_{ij}$, $E_{ijh}$, $O_{ijh}$ applied to $(\vec d,\vec b)$, for stations $i\ne j$ and any station $h$. Every neighbor is at dock-move distance exactly $1$.
--
--   **Formalization Note** The page lets $i,j,h$ range over all stations and then states that every neighbor is at $|\vec d+\vec b-\vec d'-\vec b'|_1=2$; this requires $i\ne j$, which is imposed. The third station $h$ is unrestricted.
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, §3.1, p.18 (neighborhood N)

import Mathlib
import Definitions.Def_MultimodularDocks_DockMove

namespace MultimodularDocks

/-- **The neighborhood** `N(d⃗, b⃗)` (Freund, Henderson, Shmoys, arXiv:1611.09304v5, p.18):
`a'` is a neighbor of `a` if it arises from `a` by one dock-move from a station `i` to a
different station `j`; the third station `h` of `E` and `O` is arbitrary.

**Formalization Note** The page lets `i, j, h ∈ [n]` range freely but then states that every
neighbor is at `|d⃗ + b⃗ − d⃗′ − b⃗′|₁ = 2`, which requires `i ≠ j`; for `i = j` the "dock-move"
is a bike move or the identity. The reading `i ≠ j` is used. -/
def Neighbor {S : Type*} [DecidableEq S] (a a' : Alloc S) : Prop :=
  ∃ m : DockMove S, m.src ≠ m.dst ∧ a' = m.apply a

end MultimodularDocks


