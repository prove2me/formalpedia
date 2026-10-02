-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_DomR
-- name    : DiscreteConvex_MConvexFunctionsC_DomR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:15:47.88002+00:00
-- url     : https://prove2.me/theorems/96435de7-7394-4335-8595-5b72522b079b
-- title:
--   DomR
-- statement:
--   The effective domain of a real-valued function $g : \mathbb R^V \to \mathbb R\cup\{+\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue

import Mathlib

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def DomR (g : (V → ℝ) → WithTop ℝ) : Set (V → ℝ) := {x | g x ≠ ⊤}

end DiscreteConvex.MConvexFunctionsC


