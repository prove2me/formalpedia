-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomZ
-- name    : DiscreteConvex_LConvexFunctionsD_DomZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:58:48.128894+00:00
-- url     : https://prove2.me/theorems/1cb44ee2-d18e-4cbe-a97b-7e8e5773f12b
-- title:
--   DomZ
-- statement:
--   The effective domain of $g:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The effective domain of `g : Zⱽ → R ∪ {+∞}`. -/
def DomZ (g : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {p | g p ≠ ⊤}

end DiscreteConvex.LConvexFunctionsD


