-- Prove2me | Definitions.Def_MultimodularDocks_IsOptimalP3
-- name    : MultimodularDocks_IsOptimalP3
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:32.918362+00:00
-- url     : https://prove2.me/theorems/43830cee-fd8e-4ff1-8b23-7d4b13354b47
-- title:
--   Optimality for problem (P3)
-- statement:
--   An allocation is **optimal for (P3)** if it is feasible and no feasible allocation has a smaller objective:
--
--   $$
--   \min\ c(\vec d,\vec b)\quad\text{s.t.}\quad |\vec d+\vec b|_1=D+B,\ \ |\vec b|_1=B .
--   $$
--
--   (P3) is the problem without the operational constraint on the number of moved docks.
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, §3.2, p.18 (P3)

import Mathlib
import Definitions.Def_MultimodularDocks_Feasible
import Definitions.Def_MultimodularDocks_cost

namespace MultimodularDocks

/-- **Optimality for problem (P3)** (Freund, Henderson, Shmoys, arXiv:1611.09304v5, p.18): `a` is
feasible and no feasible allocation has a smaller objective. -/
def IsOptimalP3 {S : Type*} [Fintype S] (I : Instance S) (a : Alloc S) : Prop :=
  Feasible I a ∧ ∀ y, Feasible I y → cost I a ≤ cost I y

end MultimodularDocks


