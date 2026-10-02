-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_MExchangeAxiomR
-- name    : DiscreteConvex_MConvexFunctionsC_MExchangeAxiomR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:24:42.744661+00:00
-- url     : https://prove2.me/theorems/c9d5476d-51ef-44a7-8f6c-ecae86776736
-- title:
--   MExchangeAxiomR
-- statement:
--   Axiom (M-EXC[R]): the real-variable exchange axiom for a polyhedral convex function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, axiom (M-EXC[R]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, axiom (M-EXC[R])

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_SuppPosR
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_SuppNegR
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_DomR

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (M-EXC[R]). -/
def MExchangeAxiomR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomR g, ∀ y ∈ DomR g, ∀ u ∈ SuppPosR x y, ∃ v ∈ SuppNegR x y, ∃ alpha0 : ℝ, 0 < alpha0 ∧
    ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ alpha0 →
      g x + g y ≥ g (fun w => x w - alpha * (CharVec u w - CharVec v w : ℝ)) +
        g (fun w => y w + alpha * (CharVec u w - CharVec v w : ℝ))

end DiscreteConvex.MConvexFunctionsC


