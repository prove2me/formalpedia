-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_ConvexClosureValOn
-- name    : DiscreteConvex_LConvexFunctionsD_ConvexClosureValOn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:02:02.030616+00:00
-- url     : https://prove2.me/theorems/11877aa3-73ef-4bf0-95ad-fe6125d2d94d
-- title:
--   ConvexClosureValOn
-- statement:
--   The value of a convex-combination representation of $g$ restricted to a finite point set $S$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)-adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomZ

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The value of a convex-combination representation of `g` restricted to a finite point set
`S`. -/
noncomputable def ConvexClosureValOn (g : (V → ℤ) → WithTop ℝ) (S : Finset (V → ℤ)) (x : V → ℝ) :
    WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ lam : (V → ℤ) → ℝ,
    (∀ y ∈ S, 0 ≤ lam y) ∧ (∑ y ∈ S, lam y = 1) ∧ (∀ y ∈ S, y ∈ DomZ g) ∧
    (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v) ∧
    L = ((∑ y ∈ S, lam y * (g y).untopD 0 : ℝ) : WithTop ℝ)}

end DiscreteConvex.LConvexFunctionsD


