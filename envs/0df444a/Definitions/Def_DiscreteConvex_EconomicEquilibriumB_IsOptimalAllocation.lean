-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsOptimalAllocation
-- name    : DiscreteConvex_EconomicEquilibriumB_IsOptimalAllocation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:43:59.098182+00:00
-- url     : https://prove2.me/theorems/a75268ea-b684-4f90-a6db-3e776e8221be
-- title:
--   Optimality of an allocation
-- statement:
--   $(x,y)$ is an optimal allocation of the MSFP2 associated with the economy: every bundle lies in its agent's effective domain, and no reallocation with the same aggregate excess $\sum_h x_h - \sum_l y_l$ achieves a larger total surplus $\sum_h U_h(x_h) - \sum_l C_l(y_l)$.
--
--   Theorems 11.21 and 11.22 are statements about such an allocation.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §11.5.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §11.5

import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- `(x,y)` is an optimal allocation of the MSFP2 associated with the economy: every bundle is in
its agent's effective domain, and no reallocation with the same aggregate excess achieves a larger
total surplus `∑ U_h(x_h) - ∑ C_l(y_l)`. Murota, *Discrete Convex Analysis*, SIAM 2003, §11.5
states Theorems 11.21 and 11.22 for such an allocation. -/
def IsOptimalAllocation {H L : Type*} [Fintype H] [Fintype L] (U : H → (K → ℤ) → WithBot ℝ)
    (C : L → (K → ℤ) → WithTop ℝ) (x : H → (K → ℤ)) (y : L → (K → ℤ)) : Prop :=
  (∀ h, U h (x h) ≠ ⊥) ∧ (∀ l, C l (y l) ≠ ⊤) ∧
  ∀ x' : H → (K → ℤ), ∀ y' : L → (K → ℤ),
    (∀ h, U h (x' h) ≠ ⊥) → (∀ l, C l (y' l) ≠ ⊤) →
    (∑ h, x' h) - (∑ l, y' l) = (∑ h, x h) - (∑ l, y l) →
    (∑ h, (U h (x' h)).unbotD 0) - (∑ l, (C l (y' l)).untopD 0) ≤
      (∑ h, (U h (x h)).unbotD 0) - (∑ l, (C l (y l)).untopD 0)

end DiscreteConvex.EconomicEquilibriumB


