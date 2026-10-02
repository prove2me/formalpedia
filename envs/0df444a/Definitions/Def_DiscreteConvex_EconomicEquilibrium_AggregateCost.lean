-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_AggregateCost
-- name    : DiscreteConvex_EconomicEquilibrium_AggregateCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:58:21.271867+00:00
-- url     : https://prove2.me/theorems/55043d38-3200-4f9e-a99a-46ff9a821a38
-- title:
--   Aggregate cost function $\Psi$ (Eq. 11.24)
-- statement:
--   The aggregate cost function (Eq. (11.24))
--   $$\Psi(z) = \inf\Big\{\sum_l C_l(y_l) - \sum_h U_h(x_h) \ \Big|\ \sum_h x_h - \sum_l y_l = z\Big\},$$
--   the integer infimal convolution of the producers' cost functions and the negatives of the consumers' utility functions.
--
--   **Formalization Note.** `sInf` over `WithTop ℝ` (a complete lattice) realizes the book's convention that the infimum is $+\infty$ when no feasible $(x,y)$ exists for $z$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.335, Eq. (11.24).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.335, Eq. (11.24)

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_NegUtil

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.335, Eq. (11.24): the aggregate cost function,
in `DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- The aggregate cost function (Eq. (11.24))
`Ψ(z) = inf {∑_l Cl(yl) − ∑_h Uh(xh) | ∑_h xh − ∑_l yl = z}`, the integer infimal convolution of
the producers' cost functions and the negatives of the consumers' utility functions. `sInf` over
`WithTop ℝ` (a complete lattice) realizes the book's convention that the infimum is `+∞` when no
feasible `(x, y)` exists for `z`. -/
noncomputable def AggregateCost {H K L : Type*} [Fintype H] [Fintype K] [Fintype L]
    [DecidableEq K] (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ) (z : K → ℤ) :
    WithTop ℝ :=
  sInf {v : WithTop ℝ | ∃ (x : H → (K → ℤ)) (y : L → (K → ℤ)),
    (∑ h, x h) - (∑ l, y l) = z ∧
    v = (∑ l, C l (y l)) + ∑ h, NegUtil (U h (x h))}

end DiscreteConvex.EconomicEquilibrium


