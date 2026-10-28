-- Prove2me | Definitions.Def_LL_Decomp1525c_P1V
-- name    : LL_Decomp1525c_P1V
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-28T17:02:12.214055+00:00
-- url     : https://prove2.me/theorems/5564d13a-f205-49ca-8c2a-3c9fcff48c3f
-- title:
--   Admissible odd primes
-- statement:
--   For real $x$, $P_1(x)$ is the finite set of primes $p$ with $3\le p\le\lfloor x-3\rfloor_+$, where $\lfloor\cdot\rfloor_+$ is the natural number floor.

import Mathlib
open Finset Real MeasureTheory intervalIntegral
open scoped Classical
noncomputable section
namespace LL_Decomp1525c
def P1V (x : ℝ) : Finset ℕ := (Icc 3 ⌊x - 3⌋₊).filter Nat.Prime
end LL_Decomp1525c


