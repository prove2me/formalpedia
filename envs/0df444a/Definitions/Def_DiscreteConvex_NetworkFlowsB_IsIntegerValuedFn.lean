-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_IsIntegerValuedFn
-- name    : DiscreteConvex_NetworkFlowsB_IsIntegerValuedFn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:20:57.865052+00:00
-- url     : https://prove2.me/theorems/8b49f092-60b3-48d2-af6b-582826e62866
-- title:
--   IsIntegerValuedFn
-- statement:
--   $f:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ is integer valued.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `f : Zⱽ → R ∪ {+∞}` is integer valued. -/
def IsIntegerValuedFn (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x : V → ℤ, f x = ⊤ ∨ ∃ k : ℤ, f x = ((k : ℝ) : WithTop ℝ)

end DiscreteConvex.NetworkFlowsB


