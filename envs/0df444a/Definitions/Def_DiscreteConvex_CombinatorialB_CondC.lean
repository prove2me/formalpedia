-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialB_CondC
-- name    : DiscreteConvex_CombinatorialB_CondC
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:33:14.547069+00:00
-- url     : https://prove2.me/theorems/46eb283d-6508-4fbc-bcb2-2c420d2b1af2
-- title:
--   Theorem 2.12 condition (c)
-- statement:
--   Condition (c): for any $x$ and $i\in\operatorname{supp}^+(x)$, $x^\top m_i \ge \min(0,\min_{j\in\operatorname{supp}^-(x)} x^\top m_j)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.70, Theorem 2.12(c).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.70, Theorem 2.12(c)

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialB_ColDot
import Definitions.Def_DiscreteConvex_CombinatorialB_SuppPosR
import Definitions.Def_DiscreteConvex_CombinatorialB_SuppNegR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.70, Theorem 2.12 condition (c), in
`DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- Theorem 2.12 condition **(c)**: for any `x` and `i ∈ supp⁺(x)`,
`x⊤m_i ≥ min(0, min_{j∈supp⁻(x)} x⊤m_j)`, unfolded as in `CondB`. -/
def CondC {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℝ) : Prop :=
  ∀ x : V → ℝ, ∀ i ∈ SuppPosR x,
    ColDot M x i ≥ 0 ∨ ∃ j ∈ SuppNegR x, ColDot M x i ≥ ColDot M x j

end DiscreteConvex.CombinatorialB


