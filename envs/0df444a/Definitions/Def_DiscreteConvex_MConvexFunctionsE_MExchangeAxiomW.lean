-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_MExchangeAxiomW
-- name    : DiscreteConvex_MConvexFunctionsE_MExchangeAxiomW
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:04:48.940773+00:00
-- url     : https://prove2.me/theorems/65b57899-fe8a-465f-91ee-2330f20dd162
-- title:
--   MExchangeAxiomW
-- statement:
--   Axiom (M-EXCw[Z]), the weak exchange axiom (Theorem 6.5): `∃u, ∃v` in place of `∀u, ∃v`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.135, axiom (M-EXCw[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.135, axiom (M-EXCw[Z])

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (M-EXCw[Z]), the weak exchange axiom (Theorem 6.5): `∃u, ∃v` in place of `∀u, ∃v`. -/
def MExchangeAxiomW (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ x ∈ DomZ f, ∃ y ∈ DomZ f, x ≠ y ∧ ∃ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    f x + f y ≥ f (fun w => x w - CharVec u w + CharVec v w) +
      f (fun w => y w + CharVec u w - CharVec v w)

end DiscreteConvex.MConvexFunctionsE


