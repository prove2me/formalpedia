-- Prove2me | Definitions.Def_Erdos195_TriangularBinary_Model
-- name    : Erdos195_TriangularBinary_Model
-- status  : Definition
-- author  : @xwh
-- created : 2026-10-23T08:30:56.021975+00:00
-- url     : https://prove2.me/theorems/da735e6f-b0a4-45e4-8d55-8a96ef3f722c
-- title:
--   Binary digit expansions with arbitrary integer place coefficients
-- statement:
--   For an arbitrary integer sequence $a=(a_j)_{j\ge0}$ and a nonnegative integer $n$ with binary digits $b_j(n)$, define
--   $$w_a(n)=\sum_{j\ge0}a_j2^j b_j(n).$$
--   The sum is finite. Equivalently, $w_a(0)=0$ and for $n>0$,
--   $$w_a(n)=2w_{(a_{j+1})_{j\ge0}}(\lfloor n/2\rfloor)+(n\bmod2)a_0.$$
--   No sign, magnitude, oddness, periodicity, injectivity or surjectivity condition is imposed on the coefficients or the resulting map. This is a minimal definition for a construction-family obstruction in the Erdős195 investigation; it makes no claim about the unrestricted existence problem.
-- source:
--   Research-defined exact integer-coefficient binary recursion for public Erdős195 mission49a38d9f-e723-48b5-9209-130dea45c67b. Ho arXiv2609.12780v1 provides the actual nonnegative-integer permutation used in a separately checked application. This weighted transport is an investigated extension method, not a result attributed to Ho.

import Mathlib

namespace Erdos195.TriangularWeightResearch

/-- Binary digit j has integer weight 2^j * a j. The recursion consumes
one binary digit at a time; no condition is imposed on the coefficients. -/
def weightValue (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  if hn : n = 0 then 0 else
    2 * weightValue (fun j => a (j+1)) (n/2) + if n%2=0 then 0 else a 0
termination_by n
decreasing_by omega

end Erdos195.TriangularWeightResearch


