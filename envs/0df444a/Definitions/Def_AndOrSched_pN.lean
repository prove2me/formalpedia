-- Prove2me | Definitions.Def_AndOrSched_pN
-- name    : AndOrSched_pN
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:57.800778+00:00
-- url     : https://prove2.me/theorems/b7c93ec1-2b30-41c9-92be-3951997ab762
-- title:
--   Integer processing times
-- statement:
--   The processing time $p_j$ read as a natural number $\lfloor p_j\rfloor$. It equals $p_j$ for the integer processing times of normalized instances, the only place where it is used.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.6, "all data is integer"; p.9, "all processing times are non-negative integers"

import Mathlib
import Definitions.Def_AndOrSched_Instance
open scoped Classical NNReal

namespace AndOrSched

/-- The processing time of job `j` as a natural number, for instances with integer data
(Happach, Schulz, arXiv:2001.07011v1, §2, p.6, "we may assume that all data is integer"; p.9, "recall that all processing times
are non-negative integers").

**Formalization Note** `pN I j = ⌊pⱼ⌋₊`, which equals `pⱼ` whenever `pⱼ` is an integer, the only
case in which it is used (normalized instances, `IsNormalized`). -/
def pN (I : Instance) (j : I.N) : ℕ :=
  Nat.floor (I.p j)

end AndOrSched


