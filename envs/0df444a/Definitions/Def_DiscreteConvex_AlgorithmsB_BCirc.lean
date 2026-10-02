-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_BCirc
-- name    : DiscreteConvex_AlgorithmsB_BCirc
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:02:12.09064+00:00
-- url     : https://prove2.me/theorems/7c46c283-1231-42d6-8f44-5cbda7f09a1d
-- title:
--   BCirc
-- statement:
--   $B^\circ=\{y\in B\mid \ell^\circ_B\le y\le u^\circ_B\}$, the central part of $B$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.284.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.284

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_LBCirc
import Definitions.Def_DiscreteConvex_AlgorithmsB_UBCirc

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `B° = {y∈B | ℓ°_B ≤ y ≤ u°_B}`, the central part of `B`. -/
def BCirc (B : Set (V → ℤ)) : Set (V → ℤ) :=
  {y ∈ B | ∀ v, LBCirc B v ≤ (y v : ℚ) ∧ (y v : ℚ) ≤ UBCirc B v}

end DiscreteConvex.AlgorithmsB


