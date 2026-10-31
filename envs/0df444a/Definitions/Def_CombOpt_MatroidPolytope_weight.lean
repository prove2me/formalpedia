-- Prove2me | Definitions.Def_CombOpt_MatroidPolytope_weight
-- name    : CombOpt_MatroidPolytope_weight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:44.927917+00:00
-- url     : https://prove2.me/theorems/55a7f5d5-89ad-4b00-83e5-1a4b83be6dea
-- title:
--   Weight $c(J)$ of a set
-- statement:
--   For weights $c\in\mathbb R^S$ and $J\subseteq S$, the **weight** of $J$ is
--   $$c(J)=\sum_{e\in J}c_e.$$
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, pp. 273–275 (PDF pp. 280–282)

import Mathlib

namespace CombOpt.MatroidPolytope

/-- **Weight of a set.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1, pp. 273–275 (PDF pp. 280–282): the weight of a set J with respect to
`c ∈ ℝ^S` is `c(J) = Σ_{e ∈ J} c_e`. -/
def weight {α : Type*} (c : α → ℝ) (J : Finset α) : ℝ :=
  ∑ e ∈ J, c e

end CombOpt.MatroidPolytope


