-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_UBoundJ
-- name    : DiscreteConvex_EconomicEquilibriumB_UBoundJ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:44:00.800654+00:00
-- url     : https://prove2.me/theorems/aa92ea4f-1fa5-4cb0-81ee-1a40de2ee222
-- title:
--   UBoundJ
-- statement:
--   $u(j)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.343, Eq. (11.41).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.343, Eq. (11.41)

import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- `u(j)`, Eq. (11.41). -/
noncomputable def UBoundJ {H L : Type*} [Fintype H] [Fintype L] [Nonempty H] [Nonempty L]
    (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ) (x : H → (K → ℤ))
    (y : L → (K → ℤ)) (j : K) : ℝ :=
  min
    ((Finset.univ : Finset H).inf' Finset.univ_nonempty
      (fun h => (U h (x h)).unbotD 0 - (U h (fun k => x h k - (if k = j then (1:ℤ) else 0))).unbotD 0))
    ((Finset.univ : Finset L).inf' Finset.univ_nonempty
      (fun l => (C l (fun k => y l k + (if k = j then (1:ℤ) else 0)) - C l (y l)).untopD 0))

end DiscreteConvex.EconomicEquilibriumB


