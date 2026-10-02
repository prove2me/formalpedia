-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_QM
-- name    : DiscreteConvex_MConvexFunctionsE_QM
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:07:43.103257+00:00
-- url     : https://prove2.me/theorems/04e8ec48-8524-4f26-97c1-87665d2926f8
-- title:
--   QM
-- statement:
--   Axiom (QM): $f$ is quasi M-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.169, axiom (QM).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.169, axiom (QM)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DeltaF

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (QM): `f` is quasi M-convex. -/
def QM (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    DeltaF f x v u ≤ 0 ∨ DeltaF f y u v ≤ 0

end DiscreteConvex.MConvexFunctionsE


