-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_SSQM
-- name    : DiscreteConvex_MConvexFunctionsE_SSQM
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:07:40.16647+00:00
-- url     : https://prove2.me/theorems/613dbccb-952a-4a31-beec-12b3eb020b73
-- title:
--   SSQM
-- statement:
--   Axiom (SSQM): $f$ is semistrictly quasi M-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.169, axiom (SSQM).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.169, axiom (SSQM)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DeltaF

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (SSQM): `f` is semistrictly quasi M-convex. -/
def SSQM (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    DeltaF f x v u < 0 ∨ DeltaF f y u v < 0 ∨ (DeltaF f x v u = 0 ∧ DeltaF f y u v = 0)

end DiscreteConvex.MConvexFunctionsE


