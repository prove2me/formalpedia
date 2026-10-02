-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_UBoundJE
-- name    : DiscreteConvex_EconomicEquilibriumB_UBoundJE
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:56:29.468778+00:00
-- url     : https://prove2.me/theorems/4cbfcc4e-212f-4fdc-b1f6-9a125fd81733
-- title:
--   The upper bound u(j) in the extended reals
-- statement:
--   $u(j)$ of Eq. (11.41), computed in $\overline{\mathbb{R}}$: the smaller of $\min_h [U_h(x_h)-U_h(x_h-\chi_j)]$ and $\min_l [C_l(y_l+\chi_j)-C_l(y_l)]$, so an unattainable bundle leaves the bound infinite.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §11.5, Eq. (11.41).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §11.5, Eq. (11.41)

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ToEReal
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ToERealOfBot

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- `u(j)`, Eq. (11.41), computed in `EReal` so that an unattainable bundle leaves the bound
infinite rather than `0`. -/
noncomputable def UBoundJE {H L : Type*} [Fintype H] [Fintype L] [Nonempty H] [Nonempty L]
    (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ) (x : H → (K → ℤ))
    (y : L → (K → ℤ)) (j : K) : EReal :=
  min
    ((Finset.univ : Finset H).inf' Finset.univ_nonempty
      (fun h => ToERealOfBot (U h (x h)) -
        ToERealOfBot (U h (fun k => x h k - (if k = j then (1:ℤ) else 0)))))
    ((Finset.univ : Finset L).inf' Finset.univ_nonempty
      (fun l => ToEReal (C l (fun k => y l k + (if k = j then (1:ℤ) else 0))) -
        ToEReal (C l (y l))))

end DiscreteConvex.EconomicEquilibriumB


