-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_QMw
-- name    : DiscreteConvex_MConvexFunctionsE_QMw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:07:56.725186+00:00
-- url     : https://prove2.me/theorems/e0b8178b-171b-4d1e-8130-2ce923b57bee
-- title:
--   QMw
-- statement:
--   Axiom (QMw), the weaker variant of (QM).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.170, axiom (QMw).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.170, axiom (QMw)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DeltaF

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (QMw), the weaker variant of (QM). -/
def QMw (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, x ≠ y → ∃ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    DeltaF f x v u ≤ 0 ∨ DeltaF f y u v ≤ 0

end DiscreteConvex.MConvexFunctionsE


