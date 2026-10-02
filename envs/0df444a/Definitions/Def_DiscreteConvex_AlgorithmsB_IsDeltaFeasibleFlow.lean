-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_IsDeltaFeasibleFlow
-- name    : DiscreteConvex_AlgorithmsB_IsDeltaFeasibleFlow
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:50:21.670438+00:00
-- url     : https://prove2.me/theorems/a1aa1def-c7b6-4d27-bfec-e401ec0fc930
-- title:
--   IsDeltaFeasibleFlow
-- statement:
--   $\phi:V\times V\to\mathbb R$ is a $\delta$-feasible flow.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.296, preceding Eq. (10.20).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.296, preceding Eq. (10.20)

import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `ϕ : V×V → R` is a `δ`-feasible flow. -/
def IsDeltaFeasibleFlow (delta : ℝ) (phi : V → V → ℝ) : Prop :=
  ∀ u v, 0 ≤ phi u v ∧ phi u v ≤ delta ∧ (phi u v = 0 ∨ phi v u = 0)

end DiscreteConvex.AlgorithmsB


