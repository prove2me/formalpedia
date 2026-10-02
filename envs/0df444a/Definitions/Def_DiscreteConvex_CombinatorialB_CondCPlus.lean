-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialB_CondCPlus
-- name    : DiscreteConvex_CombinatorialB_CondCPlus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:32:40.698271+00:00
-- url     : https://prove2.me/theorems/ec10a101-36ff-4dc1-a05b-6b9a5db245b4
-- title:
--   Theorem 2.12 condition (c+)
-- statement:
--   Condition (c+): for any $x$ and $i\in\operatorname{supp}^+(x)$, $x^\top m_i > \min(0,\min_{j\in\operatorname{supp}^-(x)} x^\top m_j)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.70, Theorem 2.12(c+).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.70, Theorem 2.12(c+)

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialB_ColDot
import Definitions.Def_DiscreteConvex_CombinatorialB_SuppPosR
import Definitions.Def_DiscreteConvex_CombinatorialB_SuppNegR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.70, Theorem 2.12 condition (c+), in
`DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- Theorem 2.12 condition **(c+)**: for any `x` and `i ∈ supp⁺(x)`,
`x⊤m_i > min(0, min_{j∈supp⁻(x)} x⊤m_j)`, unfolded as in `CondB`. -/
def CondCPlus {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℝ) : Prop :=
  ∀ x : V → ℝ, ∀ i ∈ SuppPosR x,
    ColDot M x i > 0 ∨ ∃ j ∈ SuppNegR x, ColDot M x i > ColDot M x j

end DiscreteConvex.CombinatorialB


