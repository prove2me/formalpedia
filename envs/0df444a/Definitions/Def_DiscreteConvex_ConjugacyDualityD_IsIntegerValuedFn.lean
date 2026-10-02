-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsIntegerValuedFn
-- name    : DiscreteConvex_ConjugacyDualityD_IsIntegerValuedFn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:56:14.793945+00:00
-- url     : https://prove2.me/theorems/58089f46-3717-403c-9553-a2ac76fc9c1b
-- title:
--   IsIntegerValuedFn
-- statement:
--   $f:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ is integer valued.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, redeclared

import Mathlib

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f : Zⱽ → R∪{+∞}` is integer valued. -/
def IsIntegerValuedFn (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x : V → ℤ, f x = ⊤ ∨ ∃ k : ℤ, f x = ((k : ℝ) : WithTop ℝ)

end DiscreteConvex.ConjugacyDualityD


