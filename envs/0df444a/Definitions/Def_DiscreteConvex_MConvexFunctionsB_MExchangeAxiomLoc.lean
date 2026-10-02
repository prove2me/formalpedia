-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiomLoc
-- name    : DiscreteConvex_MConvexFunctionsB_MExchangeAxiomLoc
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:08:26.676312+00:00
-- url     : https://prove2.me/theorems/3e93c277-4e02-4136-bd27-3e88e3b48424
-- title:
--   MExchangeAxiomLoc
-- statement:
--   Axiom **(M-EXCloc[Z])**: (M-EXC[Z]) required only for $x,y$ with $\|x-y\|_1 = 4$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.135, Eq. (6.11), axiom (M-EXCloc[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.135, Eq. (6.11), axiom (M-EXCloc[Z])

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.135, Eq. (6.11), axiom (M-EXCloc[Z]), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Axiom **(M-EXCloc[Z])**: (M-EXC[Z]) required only for `x,y` with `‖x-y‖₁ = 4`. -/
def MExchangeAxiomLoc {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, (∑ v, |x v - y v| = 4) →
    ∃ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
      f x + f y ≥ f (fun w => x w - CharVec u w + CharVec v w) +
        f (fun w => y w + CharVec u w - CharVec v w)

end DiscreteConvex.MConvexFunctionsB


