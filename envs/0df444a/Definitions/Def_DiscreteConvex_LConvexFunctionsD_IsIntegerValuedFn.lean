-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsIntegerValuedFn
-- name    : DiscreteConvex_LConvexFunctionsD_IsIntegerValuedFn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:16.791007+00:00
-- url     : https://prove2.me/theorems/35b576ae-ac96-4343-8f2e-8cde4fbf29ea
-- title:
--   IsIntegerValuedFn
-- statement:
--   $g$ is integer valued.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is integer valued. -/
def IsIntegerValuedFn (g : (V → ℤ) → WithTop ℝ) : Prop := ∀ p, ∃ k : ℤ, g p = ((k : ℝ) : WithTop ℝ)

end DiscreteConvex.LConvexFunctionsD


