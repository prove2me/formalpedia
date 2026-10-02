-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFNatR
-- name    : DiscreteConvex_LConvexFunctionsC_SBFNatR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:32:07.487026+00:00
-- url     : https://prove2.me/theorems/d6f248fb-fef9-44d5-9f0f-bab0362d8a2f
-- title:
--   SBFNatR
-- statement:
--   Axiom (SBF$^\natural$[R]), translation submodularity for polyhedral functions.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.192, axiom (SBF$^\\natural$[R]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.192, axiom (SBF$^\\natural$[R])

import Mathlib

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (SBF♮[R]), translation submodularity for polyhedral functions. -/
def SBFNatR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℝ, ∀ alpha : ℝ, 0 ≤ alpha →
    g p + g q ≥ g (fun v => max (p v - alpha) (q v)) + g (fun v => min (p v) (q v + alpha))

end DiscreteConvex.LConvexFunctionsC


