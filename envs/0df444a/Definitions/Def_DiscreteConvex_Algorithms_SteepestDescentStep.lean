-- Prove2me | Definitions.Def_DiscreteConvex_Algorithms_SteepestDescentStep
-- name    : DiscreteConvex_Algorithms_SteepestDescentStep
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:26:25.364657+00:00
-- url     : https://prove2.me/theorems/fd2be13a-6e59-4956-94f0-b10c75a8879a
-- title:
--   One step of the steepest descent algorithm (steps S1+S3, p.282)
-- statement:
--   One step of the steepest descent algorithm: $x'$ is obtained from $x$ by swapping along a steepest pair $(u,v)$, i.e. $x' = x - \chi_u + \chi_v$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_Algorithms_IsSteepestPair

open DiscreteConvex.MConvexFunctions

namespace DiscreteConvex.Algorithms

/-- One step of the steepest descent algorithm (S1 + S3, p.282): `x'` is obtained from `x` by
swapping along a steepest pair `(u,v)`. -/
def SteepestDescentStep {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (x x' : V → ℤ) : Prop :=
  ∃ u v : V, IsSteepestPair f x u v ∧ x' = fun w => x w - CharVec u w + CharVec v w

end DiscreteConvex.Algorithms


