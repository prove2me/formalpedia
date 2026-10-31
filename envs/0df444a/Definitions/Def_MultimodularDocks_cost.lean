-- Prove2me | Definitions.Def_MultimodularDocks_cost
-- name    : MultimodularDocks_cost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:35:43.631384+00:00
-- url     : https://prove2.me/theorems/f191e5c7-db40-49d0-9499-7a987a7e4020
-- title:
--   System-wide objective $c(\vec d,\vec b)=\sum_i c_i(d_i,b_i)$
-- statement:
--   The objective of an allocation is the total cost over all stations,
--
--   $$
--   c(\vec d,\vec b)=\sum_i c_i(d_i,b_i).
--   $$
--
--   **Formalization Note** The sum is of the real station costs $g_i$; on feasible allocations it is the paper's $c$, which is $+\infty$ on infeasible ones. Only costs of feasible allocations are ever compared.
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, §2, p.10 (system-wide objective)

import Mathlib
import Definitions.Def_MultimodularDocks_Instance

namespace MultimodularDocks

/-- **The system-wide objective** `c(d⃗, b⃗) = ∑_i c_i(d_i, b_i)` (Freund, Henderson, Shmoys,
arXiv:1611.09304v5, p.10).

**Formalization Note** The sum is of the real station costs `g i`; on feasible allocations
(`Feasible`) it is the page's `c`, which is `+∞` elsewhere. Every statement compares costs of
feasible allocations only. -/
def cost {S : Type*} [Fintype S] (I : Instance S) (a : Alloc S) : ℝ :=
  ∑ i, I.g i (a.d i) (a.b i)

end MultimodularDocks


