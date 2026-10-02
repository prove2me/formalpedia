-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalPotentialSetZ
-- name    : DiscreteConvex_NetworkFlowsB_OptimalPotentialSetZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:27:32.755181+00:00
-- url     : https://prove2.me/theorems/df5b511d-fec6-4973-aabc-a0bc59c823c7
-- title:
--   OptimalPotentialSetZ
-- statement:
--   The set of integer-valued optimal potentials for MSFP3.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.262, Theorem 9.16(4).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.262, Theorem 9.16(4)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMSFP3Z
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsOptimalPotentialZ

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The set of integer-valued optimal potentials for MSFP3. -/
def OptimalPotentialSetZ (tail head : A → V) (fa : A → ℤ → WithTop ℝ) (f : (V → ℤ) → WithTop ℝ) :
    Set (V → ℤ) :=
  {pZ | ∃ xi, OptimalFlowMSFP3Z tail head fa f xi ∧
    IsOptimalPotentialZ tail head fa f xi (fun v => (pZ v : ℝ))}

end DiscreteConvex.NetworkFlowsB


