-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsB_SBFNat
-- name    : DiscreteConvex_LConvexFunctionsB_SBFNat
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:20:47.398509+00:00
-- url     : https://prove2.me/theorems/05bbbe78-d6ca-4ca6-b427-ba5256d544b3
-- title:
--   SBFNat
-- statement:
--   Axiom (SBF$^\natural$[Z]), translation submodularity.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, axiom (SBF$^\\natural$[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, axiom (SBF$^\\natural$[Z])

import Mathlib

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (SBF♮[Z]), translation submodularity. -/
def SBFNat (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℤ, ∀ alpha : ℤ, 0 ≤ alpha →
    g p + g q ≥ g (fun v => max (p v - alpha) (q v)) + g (fun v => min (p v) (q v + alpha))

end DiscreteConvex.LConvexFunctionsB


