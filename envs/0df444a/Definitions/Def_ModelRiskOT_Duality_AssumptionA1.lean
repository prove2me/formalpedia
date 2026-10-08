-- Prove2me | Definitions.Def_ModelRiskOT_Duality_AssumptionA1
-- name    : ModelRiskOT_Duality_AssumptionA1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:53:39.438208+00:00
-- url     : https://prove2.me/theorems/f217f2fe-21cb-4a8b-b7ee-358a5d285e56
-- title:
--   Assumption (A1) — nonnegative lower semicontinuous cost vanishing exactly on the diagonal
-- statement:
--   Let $S$ be a topological space. A function $c : S\times S\to\mathbb R$ satisfies **Assumption (A1)** if
--
--   1. $c(x,y)\ge 0$ for all $x,y\in S$;
--   2. $c$ is lower semicontinuous on $S\times S$;
--   3. $c(x,y)=0$ if and only if $x=y$.
--
--   The number $c(x,y)$ is the cost of transporting a unit of mass from $x$ to $y$. Every result of the mission assumes (A1); the cost is finite-valued throughout.
--
--   **Formalization Note** The cost is curried, `c x y` $=c(x,y)$, and lower semicontinuity is that of the uncurried map on the product topology.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 4, Assumption 1 (A1)

import Mathlib

namespace ModelRiskOT.Duality

/-- **Assumption 1 (A1)** of Blanchet & Murthy, *Quantifying Distributional Model Risk via
Optimal Transport*, arXiv:1604.01446v2, p. 4: the transport cost `c : S × S → ℝ₊` is a
nonnegative, lower semicontinuous function with `c(x, y) = 0` if and only if `x = y`.
The cost is real-valued (finite); it is written curried, `c x y = c(x, y)`. -/
structure AssumptionA1 {S : Type*} [TopologicalSpace S] (c : S → S → ℝ) : Prop where
  /-- `c ≥ 0`. -/
  nonneg : ∀ x y, 0 ≤ c x y
  /-- `c` is lower semicontinuous on `S × S` (product topology). -/
  lsc : LowerSemicontinuous (fun p : S × S => c p.1 p.2)
  /-- `c(x, y) = 0` if and only if `x = y`. -/
  eq_zero_iff : ∀ x y, c x y = 0 ↔ x = y

end ModelRiskOT.Duality


