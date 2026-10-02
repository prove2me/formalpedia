-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_EquilibriumPriceSet
-- name    : DiscreteConvex_EconomicEquilibrium_EquilibriumPriceSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:17:17.914723+00:00
-- url     : https://prove2.me/theorems/c2d5e1c3-fbec-4959-acef-bec4023e7528
-- title:
--   Equilibrium price set $P^*(x^\circ)$ (Eq. 11.23)
-- statement:
--   The set $P^*(x^\circ)$ (Eq. (11.23)) of all equilibrium price vectors for total initial endowment $x^\circ$: those $p$ for which some allocation $(x,y)$ makes $((x_h \mid h), (y_l \mid l), p)$ an equilibrium.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.335, Eq. (11.23).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.335, Eq. (11.23)

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_IsEquilibrium

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.335, Eq. (11.23) (notation `P*(x°)`, used
throughout section 11.4, e.g. Theorem 11.16, p.339): the set of all equilibrium price vectors, in
`DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- The set `P*(x°)` (Eq. (11.23)) of all equilibrium price vectors for total initial endowment
`x°`: those `p` for which some allocation `(x, y)` makes `((x h | h), (y l | l), p)` an
equilibrium. -/
def EquilibriumPriceSet {H K L : Type*} [Fintype H] [Fintype K] [Fintype L]
    (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ) (x0 : K → ℤ) : Set (K → ℝ) :=
  {p | ∃ (x : H → (K → ℤ)) (y : L → (K → ℤ)), IsEquilibrium U C x0 x y p}

end DiscreteConvex.EconomicEquilibrium


