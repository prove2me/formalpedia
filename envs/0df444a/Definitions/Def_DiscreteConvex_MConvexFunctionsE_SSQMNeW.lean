-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_SSQMNeW
-- name    : DiscreteConvex_MConvexFunctionsE_SSQMNeW
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:08:18.636805+00:00
-- url     : https://prove2.me/theorems/2d4f85fc-a12c-4d6a-8d94-d1293058808c
-- title:
--   SSQMNeW
-- statement:
--   Axiom (SSQM$\ne_w$), the weaker variant of (SSQM$\ne$).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.173, axiom (SSQM$\\ne_w$).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.173, axiom (SSQM$\\ne_w$)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DeltaF

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (SSQM≠_w), the weaker variant of (SSQM≠). -/
def SSQMNeW (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, f x ≠ f y → ∃ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    DeltaF f x v u < 0 ∨ DeltaF f y u v < 0 ∨ (DeltaF f x v u = 0 ∧ DeltaF f y u v = 0)

end DiscreteConvex.MConvexFunctionsE


