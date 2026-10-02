-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_SSQMw
-- name    : DiscreteConvex_MConvexFunctionsE_SSQMw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:07:48.860799+00:00
-- url     : https://prove2.me/theorems/96b33d6f-5e9e-483b-9c81-e66b02714c5f
-- title:
--   SSQMw
-- statement:
--   Axiom (SSQMw), the weaker variant of (SSQM).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.170, axiom (SSQMw).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.170, axiom (SSQMw)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DeltaF

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (SSQMw), the weaker variant of (SSQM). -/
def SSQMw (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, x ≠ y → ∃ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    DeltaF f x v u < 0 ∨ DeltaF f y u v < 0 ∨ (DeltaF f x v u = 0 ∧ DeltaF f y u v = 0)

end DiscreteConvex.MConvexFunctionsE


