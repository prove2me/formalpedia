-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialB_CondB
-- name    : DiscreteConvex_CombinatorialB_CondB
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:32:24.445478+00:00
-- url     : https://prove2.me/theorems/0252ba24-2825-4d22-bde8-4c168dcd220b
-- title:
--   Theorem 2.12 condition (b)
-- statement:
--   Condition (b): for any $x$ and $i\in\operatorname{supp}^+(x)$, $x^\top m_i \ge \min(0,\min_{j\ne i} x^\top m_j)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.70, Theorem 2.12(b).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.70, Theorem 2.12(b)

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialB_ColDot
import Definitions.Def_DiscreteConvex_CombinatorialB_SuppPosR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.70, Theorem 2.12 condition (b), in
`DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- Theorem 2.12 condition **(b)**: for any `x` and `i ∈ supp⁺(x)`,
`x⊤m_i ≥ min(0, min_{j≠i} x⊤m_j)`, unfolded as the equivalent disjunction (valid since a real
number dominates a min of two values iff it dominates one of them, and the empty-min
convention `min ∅ = +∞` is matched by the existential being vacuously false). -/
def CondB {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℝ) : Prop :=
  ∀ x : V → ℝ, ∀ i ∈ SuppPosR x,
    ColDot M x i ≥ 0 ∨ ∃ j : V, j ≠ i ∧ ColDot M x i ≥ ColDot M x j

end DiscreteConvex.CombinatorialB


