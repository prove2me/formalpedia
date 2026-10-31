-- Prove2me | Definitions.Def_MultimodularDocks_dockGap
-- name    : MultimodularDocks_dockGap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:35:36.09981+00:00
-- url     : https://prove2.me/theorems/af3d2c5c-e5ce-40c7-bdd7-b85261946ffb
-- title:
--   Twice the dock-move distance, $|\vec d+\vec b-\vec d'-\vec b'|_1$
-- statement:
--   For two allocations,
--
--   $$
--   \mathrm{dockGap}\bigl((\vec d,\vec b),(\vec d',\vec b')\bigr)=|\vec d+\vec b-\vec d'-\vec b'|_1=\sum_i\bigl|(d_i+b_i)-(d'_i+b'_i)\bigr|.
--   $$
--
--   Half of it is the **dock-move distance**, the number of docks that must be moved to turn one allocation into the other, ignoring how each station's docks are split into bikes and empty docks. The set $S_r$ of allocations at dock-move distance at most $r$ from $(\vec d,\vec b)$ is given by $\mathrm{dockGap}\le 2r$.
--
--   **Formalization Note** The doubled quantity is used so that nothing is divided.
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, Definition 2, p.11; S_r, p.49

import Mathlib
import Definitions.Def_MultimodularDocks_Instance

namespace MultimodularDocks

/-- **Twice the dock-move distance** (Freund, Henderson, Shmoys, arXiv:1611.09304v5,
Definition 2, p.11; `S_r`, p.49): `|d⃗ + b⃗ − d⃗′ − b⃗′|₁ = ∑_i |(d_i + b_i) − (d′_i + b′_i)|`.
The dock-move distance is half of it, so "dock-move distance at most `r`" is
`dockGap a a' ≤ 2 * r`.

**Formalization Note** The distance ignores how the docks of a station are split between
bikes and empty docks. It is kept doubled so that nothing is divided. -/
def dockGap {S : Type*} [Fintype S] (a a' : Alloc S) : ℤ :=
  ∑ i, |dockCount a i - dockCount a' i|

end MultimodularDocks


