-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomZ
-- name    : DiscreteConvex_ConjugacyDualityB_DomZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:26:34.921037+00:00
-- url     : https://prove2.me/theorems/8bc96825-a8dd-4d25-bf82-693fb80338f3
-- title:
--   DomZ
-- statement:
--   The effective domain of $f:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, Chapter 8.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, Chapter 8

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The effective domain of `f : Zⱽ → R ∪ {+∞}`. -/
def DomZ (f : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {x | f x ≠ ⊤}

end DiscreteConvex.ConjugacyDualityB


