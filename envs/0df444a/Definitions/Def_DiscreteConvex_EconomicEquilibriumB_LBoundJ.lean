-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_LBoundJ
-- name    : DiscreteConvex_EconomicEquilibriumB_LBoundJ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:44:04.077997+00:00
-- url     : https://prove2.me/theorems/39ae6896-7355-4877-8118-18b31d8400ed
-- title:
--   LBoundJ
-- statement:
--   $\ell(j)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.343, Eq. (11.40).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.343, Eq. (11.40)

import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- `ℓ(j)`, Eq. (11.40). -/
noncomputable def LBoundJ {H L : Type*} [Fintype H] [Fintype L] [Nonempty H] [Nonempty L]
    (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ) (x : H → (K → ℤ))
    (y : L → (K → ℤ)) (j : K) : ℝ :=
  max
    ((Finset.univ : Finset H).sup' Finset.univ_nonempty
      (fun h => (U h (fun k => x h k + (if k = j then (1:ℤ) else 0))).unbotD 0 - (U h (x h)).unbotD 0))
    ((Finset.univ : Finset L).sup' Finset.univ_nonempty
      (fun l => (C l (y l) - C l (fun k => y l k - (if k = j then (1:ℤ) else 0))).untopD 0))

end DiscreteConvex.EconomicEquilibriumB


