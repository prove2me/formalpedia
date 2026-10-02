-- Prove2me | Definitions.Def_DiscreteConvex_Algorithms_SteepestDescentStepTieBreak
-- name    : DiscreteConvex_Algorithms_SteepestDescentStepTieBreak
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:32:48.524457+00:00
-- url     : https://prove2.me/theorems/c8c4695e-da65-47d4-89f6-06bc2ff4b56d
-- title:
--   One step with tie-breaking rule (Eq. 10.2)
-- statement:
--   One step of the steepest descent algorithm with the tie-breaking rule (10.2): $x'$ is obtained from $x$ by swapping along a steepest pair chosen by the rule.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282, Eq. (10.2).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282, Eq. (10.2)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_Algorithms_IsSteepestPairTieBreak

open DiscreteConvex.MConvexFunctions

namespace DiscreteConvex.Algorithms

/-- One step of the steepest descent algorithm with tie-breaking rule (10.2). -/
def SteepestDescentStepTieBreak {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (φ : V → ℕ) (x x' : V → ℤ) : Prop :=
  ∃ u v : V, IsSteepestPairTieBreak f φ x u v ∧ x' = fun w => x w - CharVec u w + CharVec v w

end DiscreteConvex.Algorithms


