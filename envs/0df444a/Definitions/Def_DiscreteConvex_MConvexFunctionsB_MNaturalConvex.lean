-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNaturalConvex
-- name    : DiscreteConvex_MConvexFunctionsB_MNaturalConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:09:28.733983+00:00
-- url     : https://prove2.me/theorems/7e149c51-49af-49f0-aee5-8b01101dc467
-- title:
--   MNaturalConvex
-- statement:
--   $f$ is **M$^\natural$-convex**: its lift $\tilde f$ (Eq. (6.4)) is an M-convex function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_LiftedFunction
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.134, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- `f : Zⱽ → R ∪ {+∞}` is **M♮-convex**: its lift `f̃` (Eq. (6.4)) is an M-convex function. -/
def MNaturalConvex {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) : Prop :=
  MExchangeAxiom (LiftedFunction f)

end DiscreteConvex.MConvexFunctionsB


