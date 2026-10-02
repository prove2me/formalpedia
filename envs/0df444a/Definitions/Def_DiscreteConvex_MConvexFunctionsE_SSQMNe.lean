-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_SSQMNe
-- name    : DiscreteConvex_MConvexFunctionsE_SSQMNe
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:08:10.453277+00:00
-- url     : https://prove2.me/theorems/8291f504-cb3b-4c0d-bcbb-7c7152311baa
-- title:
--   SSQMNe
-- statement:
--   Axiom (SSQM$\ne$), the variant of (SSQM) relevant to minimization.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.173, axiom (SSQM$\\ne$).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.173, axiom (SSQM$\\ne$)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DeltaF

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (SSQM≠), the variant of (SSQM) relevant to minimization. -/
def SSQMNe (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, f x ≠ f y → ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    DeltaF f x v u < 0 ∨ DeltaF f y u v < 0 ∨ (DeltaF f x v u = 0 ∧ DeltaF f y u v = 0)

end DiscreteConvex.MConvexFunctionsE


