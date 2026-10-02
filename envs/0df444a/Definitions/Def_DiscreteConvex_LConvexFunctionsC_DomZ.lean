-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_DomZ
-- name    : DiscreteConvex_LConvexFunctionsC_DomZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:31:36.182121+00:00
-- url     : https://prove2.me/theorems/2e004840-e856-42bb-81c6-db08034b74d5
-- title:
--   DomZ
-- statement:
--   The effective domain of $g:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177

import Mathlib

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The effective domain of `g : Zⱽ → R ∪ {+∞}`. -/
def DomZ (g : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {p | g p ≠ ⊤}

end DiscreteConvex.LConvexFunctionsC


