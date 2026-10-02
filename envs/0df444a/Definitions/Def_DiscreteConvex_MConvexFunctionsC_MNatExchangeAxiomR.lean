-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNatExchangeAxiomR
-- name    : DiscreteConvex_MConvexFunctionsC_MNatExchangeAxiomR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:30:22.305954+00:00
-- url     : https://prove2.me/theorems/98ac43d7-a3c8-46bb-be96-ac6bb9ac9fcc
-- title:
--   MNatExchangeAxiomR
-- statement:
--   Axiom (M$^\natural$-EXC[R]): the direct real-variable M$^\natural$ exchange axiom.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, axiom (M-nat-EXC[R]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, axiom (M-nat-EXC[R])

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_SuppPosR
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_SuppNegR
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_DomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_CharVecOptR

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (M♮-EXC[R]). -/
def MNatExchangeAxiomR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomR g, ∀ y ∈ DomR g, ∀ u ∈ SuppPosR x y,
    ∃ v : Option V, (v = none ∨ ∃ v' : V, v = some v' ∧ v' ∈ SuppNegR x y) ∧
    ∃ alpha0 : ℝ, 0 < alpha0 ∧
    ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ alpha0 →
      g x + g y ≥ g (fun w => x w - alpha * (CharVec u w - CharVecOptR v w)) +
        g (fun w => y w + alpha * (CharVec u w - CharVecOptR v w))

end DiscreteConvex.MConvexFunctionsC


