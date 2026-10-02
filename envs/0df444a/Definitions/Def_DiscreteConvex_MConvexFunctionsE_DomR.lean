-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomR
-- name    : DiscreteConvex_MConvexFunctionsE_DomR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:03:56.206275+00:00
-- url     : https://prove2.me/theorems/ec8419ac-1717-4e1d-a3d1-083ecc713115
-- title:
--   DomR
-- statement:
--   The effective domain of a real-valued function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue

import Mathlib

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The effective domain of a real-valued function. -/
def DomR (g : (V → ℝ) → WithTop ℝ) : Set (V → ℝ) := {x | g x ≠ ⊤}

end DiscreteConvex.MConvexFunctionsE


