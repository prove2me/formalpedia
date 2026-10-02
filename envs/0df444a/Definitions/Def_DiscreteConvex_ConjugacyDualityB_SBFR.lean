-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_SBFR
-- name    : DiscreteConvex_ConjugacyDualityB_SBFR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:27:33.298455+00:00
-- url     : https://prove2.me/theorems/c76ed09d-b6a6-414a-a014-208c74a3eb38
-- title:
--   SBFR
-- statement:
--   Axiom (SBF[R]): submodularity of a polyhedral convex function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190, axiom (SBF[R]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190, axiom (SBF[R])

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (SBF[R]): submodularity of a polyhedral convex function. -/
def SBFR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℝ, g p + g q ≥ g (p ⊔ q) + g (p ⊓ q)

end DiscreteConvex.ConjugacyDualityB


