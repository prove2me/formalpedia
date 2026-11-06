-- Prove2me | Definitions.Def_FlexibleNRM_assortmentValue
-- name    : FlexibleNRM_assortmentValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:25:40.562075+00:00
-- url     : https://prove2.me/theorems/b3d659e1-12c5-47dc-a994-6901f97816ba
-- title:
--   The expected net revenue of an assortment, the objective of (2), (7) and (11)
-- statement:
--   For a continuation value $V$, a period $t$, a state $x$ and an assortment $S$, this is
--   $$\sum_{j\in\mathcal J}\phi_{jt}(S)\,\mathbf 1_{(\mathcal F(x+e_j)\ne\emptyset)}\big[f_j+V(x+e_j)-V(x)\big],$$
--   where $e_j$ is the $j$-th unit vector. A purchase that cannot be routed earns nothing and leaves the state unchanged.
--
--   The dynamic program (2), the approximate policy (7) and the policy evaluation (11) all use this expression, with $V=J_{t+1}$, $V=\hat J_{t+1}$ and $V=U_{t+1}$.
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, Eq. (2) second line, p.8; Eq. (7), p.11; Eq. (11), p.16

import Mathlib
import Definitions.Def_FlexibleNRM_Feasible

namespace FlexibleNRM

open scoped Classical in
/-- The objective shared by (2), (7) and (11): for a continuation value `V`, the expected net
revenue of offering `S` at period `t` in state `x`,
`∑_j φ_jt(S) 1(F(x + e_j) ≠ ∅) [f_j + V(x + e_j) − V(x)]`.

Zhu, Topaloglu, manuscript of November 16, 2022, Eq. (2) second line, p.8; Eq. (7), p.11;
Eq. (11), p.16.

**Formalization Note** The indicator of `F(x + e_j) ≠ ∅` is a classical `if`. At an infeasible
`x + e_j` the value `V (x + e_j)` is multiplied by `0`, so a junk value of `V` there is never
seen. -/
noncomputable def assortmentValue {n m r : ℕ} (N : Network n m r) (t : ℕ)
    (V : (Fin n → ℕ) → ℝ) (x : Fin n → ℕ) (S : Finset (Fin n)) : ℝ :=
  ∑ j, (N.φ t).prob S j * (if Feasible N (x + Pi.single j 1) then 1 else 0) *
    (N.f j + V (x + Pi.single j 1) - V x)

end FlexibleNRM


