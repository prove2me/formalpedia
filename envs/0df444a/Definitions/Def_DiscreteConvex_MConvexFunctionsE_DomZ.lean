-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
-- name    : DiscreteConvex_MConvexFunctionsE_DomZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:03:28.724983+00:00
-- url     : https://prove2.me/theorems/6edbce49-3875-4945-a8d2-3a6da0bd5e8c
-- title:
--   DomZ
-- statement:
--   The effective domain of $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133

import Mathlib

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The effective domain of an integer-domain function. -/
def DomZ (f : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) := {x | f x ≠ ⊤}

end DiscreteConvex.MConvexFunctionsE


