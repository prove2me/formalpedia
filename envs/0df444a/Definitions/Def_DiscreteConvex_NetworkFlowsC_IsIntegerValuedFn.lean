-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_IsIntegerValuedFn
-- name    : DiscreteConvex_NetworkFlowsC_IsIntegerValuedFn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:48:26.878456+00:00
-- url     : https://prove2.me/theorems/daa9f63d-e337-4de1-b2a4-f214d7bbd4d9
-- title:
--   IsIntegerValuedFn
-- statement:
--   $f:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ is integer valued.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def IsIntegerValuedFn (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x : V → ℤ, f x = ⊤ ∨ ∃ k : ℤ, f x = ((k : ℝ) : WithTop ℝ)

end DiscreteConvex.NetworkFlowsC


