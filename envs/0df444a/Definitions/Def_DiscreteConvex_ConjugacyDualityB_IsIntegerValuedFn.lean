-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsIntegerValuedFn
-- name    : DiscreteConvex_ConjugacyDualityB_IsIntegerValuedFn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:27:30.753841+00:00
-- url     : https://prove2.me/theorems/dd835fd0-60b0-42ab-9556-b954c2683331
-- title:
--   IsIntegerValuedFn
-- statement:
--   $f:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ is integer valued.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, redeclared

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f : Zⱽ → R∪{+∞}` is integer valued. -/
def IsIntegerValuedFn (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x : V → ℤ, f x = ⊤ ∨ ∃ k : ℤ, f x = ((k : ℝ) : WithTop ℝ)

end DiscreteConvex.ConjugacyDualityB


