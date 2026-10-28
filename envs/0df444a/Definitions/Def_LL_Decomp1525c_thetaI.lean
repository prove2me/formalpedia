-- Prove2me | Definitions.Def_LL_Decomp1525c_thetaI
-- name    : LL_Decomp1525c_thetaI
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-28T17:03:03.965736+00:00
-- url     : https://prove2.me/theorems/a29e478d-88a9-48be-8bc3-f8cfd03c01d0
-- title:
--   Moving interval prime logarithm sum
-- statement:
--   For real $x,u$, define $I_x(u)=\sum_{p\in P_1(x),\ x-p<u\le2x-p}\log p$.

import Mathlib
import Definitions.Def_LL_Decomp1525c_P1V
open Finset Real MeasureTheory intervalIntegral
open scoped Classical
noncomputable section
namespace LL_Decomp1525c
def thetaI (x u : ℝ) : ℝ :=
  ∑ p ∈ (P1V x).filter (fun p : ℕ => x - p < u ∧ u ≤ 2 * x - p), Real.log p
end LL_Decomp1525c


