-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_DomR
-- name    : DiscreteConvex_MConvexFunctionsD_DomR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:48:38.891253+00:00
-- url     : https://prove2.me/theorems/b0a4425f-e195-4553-8325-1c6cc9507918
-- title:
--   DomR
-- statement:
--   The effective domain of a real-valued function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, real-variable analogue

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def DomR (g : (V → ℝ) → WithTop ℝ) : Set (V → ℝ) := {x | g x ≠ ⊤}

end DiscreteConvex.MConvexFunctionsD


