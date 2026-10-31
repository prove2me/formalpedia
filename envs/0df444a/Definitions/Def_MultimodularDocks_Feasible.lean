-- Prove2me | Definitions.Def_MultimodularDocks_Feasible
-- name    : MultimodularDocks_Feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:35:40.706231+00:00
-- url     : https://prove2.me/theorems/f6948136-2846-4893-b4a3-0487a924221d
-- title:
--   Feasible allocations of problem (P3)
-- statement:
--   Station $i$'s **band** is the set of $(d,b)$ with $d\ge 0$, $b\ge 0$ and $l_i\le d+b\le u_i$, where its cost is finite. An allocation is **feasible** for problem (P3) if every station is in its band and
--
--   $$
--   \sum_i b_i=B,\qquad \sum_i (d_i+b_i)=D+B .
--   $$
--
--   These are the constraints $|\vec b|_1=B$ and $|\vec d+\vec b|_1=D+B$ of (P3), together with the station bounds that the paper encodes as an infinite cost.
--
--   **Formalization Note** The $\ell_1$-norms are plain sums because all entries are nonnegative.
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, p.11 (station bounds, c_i = ∞ off the band) and p.18 (P3)

import Mathlib
import Definitions.Def_MultimodularDocks_Instance

namespace MultimodularDocks

/-- The band of station `i` (Freund, Henderson, Shmoys, arXiv:1611.09304v5, p.11):
`d ≥ 0`, `b ≥ 0`, `l_i ≤ d + b ≤ u_i`, the set where the station cost `c_i` is finite. -/
def InBand {S : Type*} (I : Instance S) (i : S) (d b : ℤ) : Prop :=
  0 ≤ d ∧ 0 ≤ b ∧ I.l i ≤ d + b ∧ d + b ≤ I.u i

/-- **Feasibility for problem (P3)** (Freund, Henderson, Shmoys, arXiv:1611.09304v5, p.18, with
the station bounds of p.11): every station is in its band, `|b⃗|₁ = B` and
`|d⃗ + b⃗|₁ = D + B`.

**Formalization Note** The page's (P3) minimizes `c` with `c_i = +∞` off the band; an
allocation with finite objective is exactly one satisfying the band constraints, which are
therefore part of feasibility. The `ℓ₁`-norms are plain sums because all entries are `≥ 0`. -/
def Feasible {S : Type*} [Fintype S] (I : Instance S) (a : Alloc S) : Prop :=
  (∀ i, InBand I i (a.d i) (a.b i)) ∧ ∑ i, a.b i = I.B ∧ ∑ i, dockCount a i = I.D + I.B

end MultimodularDocks


