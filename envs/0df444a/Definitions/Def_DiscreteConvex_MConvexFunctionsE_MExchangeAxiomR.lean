-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_MExchangeAxiomR
-- name    : DiscreteConvex_MConvexFunctionsE_MExchangeAxiomR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:05:23.86392+00:00
-- url     : https://prove2.me/theorems/c55895bf-378e-41ef-ae46-b5d747696bea
-- title:
--   MExchangeAxiomR
-- statement:
--   Axiom (M-EXC[R]): the real-variable M-convexity exchange axiom for a polyhedral convex function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, axiom (M-EXC[R]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, axiom (M-EXC[R])

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppPosR
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppNegR
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomR

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (M-EXC[R]): the real-variable M-convexity exchange axiom for a polyhedral convex
function. -/
def MExchangeAxiomR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomR g, ∀ y ∈ DomR g, ∀ u ∈ SuppPosR x y, ∃ v ∈ SuppNegR x y, ∃ alpha0 : ℝ, 0 < alpha0 ∧
    ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ alpha0 →
      g x + g y ≥ g (fun w => x w - alpha * (CharVec u w - CharVec v w : ℝ)) +
        g (fun w => y w + alpha * (CharVec u w - CharVec v w : ℝ))

end DiscreteConvex.MConvexFunctionsE


