-- Prove2me | Definitions.Def_LL_Decomp1525c_mainIntegralV
-- name    : LL_Decomp1525c_mainIntegralV
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-28T17:02:33.665928+00:00
-- url     : https://prove2.me/theorems/7411fd91-1489-4400-aca3-7ceebea811e2
-- title:
--   Main integral for the first moment
-- statement:
--   For real $x$, define $M(x)=\int_3^x u/\log u\,du+\int_x^{2x}(2x-u)/\log u\,du$, using oriented interval integrals.

import Mathlib
open Finset Real MeasureTheory intervalIntegral
open scoped Classical
noncomputable section
namespace LL_Decomp1525c
def mainIntegralV (x : ℝ) : ℝ :=
  (∫ u in (3 : ℝ)..x, u / Real.log u) + ∫ u in x..(2 * x), (2 * x - u) / Real.log u
end LL_Decomp1525c


