-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsIntegerValuedGamma
-- name    : DiscreteConvex_MConvexFunctionsD_IsIntegerValuedGamma
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:49:22.73689+00:00
-- url     : https://prove2.me/theorems/9daccd78-187c-4c3c-9821-ba2b680a2c95
-- title:
--   IsIntegerValuedGamma
-- statement:
--   $\gamma$ is integer valued.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `γ` is integer valued. -/
def IsIntegerValuedGamma (γ : V → V → WithTop ℝ) : Prop :=
  ∀ u v, γ u v = ⊤ ∨ ∃ k : ℤ, γ u v = ((k : ℝ) : WithTop ℝ)

end DiscreteConvex.MConvexFunctionsD


