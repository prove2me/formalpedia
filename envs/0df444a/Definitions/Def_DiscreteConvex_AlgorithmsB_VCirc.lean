-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_VCirc
-- name    : DiscreteConvex_AlgorithmsB_VCirc
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:03:01.29968+00:00
-- url     : https://prove2.me/theorems/353786a6-2611-42fb-8a60-f68d9c968f88
-- title:
--   VCirc
-- statement:
--   $V^\circ(x)=\{v\in V\mid \ell^\circ_B(v)\le x(v)\le u^\circ_B(v)\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.285.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.285

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_LBCirc
import Definitions.Def_DiscreteConvex_AlgorithmsB_UBCirc
import Definitions.Def_DiscreteConvex_AlgorithmsB_Submodular

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `V°(x) = {v∈V | ℓ°_B(v) ≤ x(v) ≤ u°_B(v)}`. -/
noncomputable def VCirc (B : Set (V → ℤ)) (x : V → ℤ) : Finset V :=
  Finset.univ.filter (fun v => LBCirc B v ≤ (x v : ℚ) ∧ (x v : ℚ) ≤ UBCirc B v)

-- ===== Submodular set functions and base polyhedra (§10.2.1) =====

end DiscreteConvex.AlgorithmsB


