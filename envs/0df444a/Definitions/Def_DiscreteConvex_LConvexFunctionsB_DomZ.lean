-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsB_DomZ
-- name    : DiscreteConvex_LConvexFunctionsB_DomZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:20:32.565997+00:00
-- url     : https://prove2.me/theorems/979f1d4b-6162-41c3-a28b-9244d1ce57ab
-- title:
--   DomZ
-- statement:
--   The effective domain of $g:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177

import Mathlib

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The effective domain of `g : Zⱽ → R ∪ {+∞}`. -/
def DomZ (g : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {p | g p ≠ ⊤}

end DiscreteConvex.LConvexFunctionsB


