-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_DomZ
-- name    : DiscreteConvex_ConjugacyDualityD_DomZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:55:28.260312+00:00
-- url     : https://prove2.me/theorems/4d803833-98be-4bb5-8fe5-25148123d570
-- title:
--   DomZ
-- statement:
--   The effective domain of $f:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, Chapter 8, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, Chapter 8, redeclared

import Mathlib

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The effective domain of `f : Zⱽ → R ∪ {+∞}`. -/
def DomZ (f : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {x | f x ≠ ⊤}

end DiscreteConvex.ConjugacyDualityD


