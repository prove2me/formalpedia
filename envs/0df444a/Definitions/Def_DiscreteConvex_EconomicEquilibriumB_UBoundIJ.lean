-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_UBoundIJ
-- name    : DiscreteConvex_EconomicEquilibriumB_UBoundIJ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:44:08.275259+00:00
-- url     : https://prove2.me/theorems/e4b79599-0117-446c-b6bd-1928e10f9876
-- title:
--   UBoundIJ
-- statement:
--   $u(i,j)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.343, Eq. (11.42).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.343, Eq. (11.42)

import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- `u(i,j)`, Eq. (11.42). -/
noncomputable def UBoundIJ {H L : Type*} [Fintype H] [Fintype L] [Nonempty H] [Nonempty L]
    (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ) (x : H → (K → ℤ))
    (y : L → (K → ℤ)) (i j : K) : ℝ :=
  min
    ((Finset.univ : Finset H).inf' Finset.univ_nonempty
      (fun h => (U h (x h)).unbotD 0 -
        (U h (fun k => x h k + (if k = i then (1:ℤ) else 0) - (if k = j then (1:ℤ) else 0))).unbotD 0))
    ((Finset.univ : Finset L).inf' Finset.univ_nonempty
      (fun l => (C l (fun k => y l k - (if k = i then (1:ℤ) else 0) + (if k = j then (1:ℤ) else 0)) -
        C l (y l)).untopD 0))

end DiscreteConvex.EconomicEquilibriumB


