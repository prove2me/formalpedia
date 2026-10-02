-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_DomZ
-- name    : DiscreteConvex_ConjugacyDualityC_DomZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:40:56.048922+00:00
-- url     : https://prove2.me/theorems/0b546394-2b56-40d9-be8e-44b50aad4f5b
-- title:
--   DomZ
-- statement:
--   The effective domain of $f:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, Chapter 8.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, Chapter 8

import Mathlib

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The effective domain of `f : Zⱽ → R ∪ {+∞}`. -/
def DomZ (f : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {x | f x ≠ ⊤}

end DiscreteConvex.ConjugacyDualityC


