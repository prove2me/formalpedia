-- Prove2me | Definitions.Def_Arithmetic
-- name    : Arithmetic
-- status  : Definition
-- author  : @harry
-- created : 2026-10-04T03:42:26.564504+00:00
-- url     : https://prove2.me/theorems/7d3c4b21-230f-4802-a70f-c8a654f8128a
-- title:
--   Integer square-sum and cell-defect formulas
-- statement:
--   For m > 0, minSquares(m,s) encodes the balanced integer square sum: with q = ⌊s/m⌋ and r = s mod m, it is m q² + (2q+1)r. The total Lean function is defined for integer m and s, while its stated minimization meaning is intended for positive m. cellBound(p) combines 1 + 2(p−11)², the 12-coordinate terms minSquares(12,12−2p) and twice minSquares(12,48−5p), and minSquares(60,10p−120); cellDefect(p) is max(0, ⌊(cellBound(p)−26)/14⌋), an arithmetic quantity rather than a proved bound here.
-- source:
--   Exact original Lean source: formalization/2026-10-03/cubic-metric/Arithmetic.lean#L7-10, 103-106, 108-109; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 cb5b20612f4683979bcf4f2a036ef30d4d5e2d3249e2bddfc63443bdcca909b4. Canonical generated Definition: Definitions/Def_Arithmetic.lean; generated SHA-256 486d920d259f2d8513b7235de9699307b87939d6882500b56f0fe3c5e016c678; Lab Git revision 828ddd31ceedab4a682c717ba51e7e526a17126a, path suites/formal-geometry/generated-project-fixtures/cubic-metric/Definitions/Def_Arithmetic.lean.

import Mathlib

set_option autoImplicit false

namespace Conway99Formal.CubicMetric

/-- The minimum square sum of `m` integer coordinates with prescribed sum `s`,
as given by Euclidean division. This definition is used only at positive `m`. -/
def minSquares (m s : ℤ) : ℤ :=
  m * (s / m) ^ 2 + (2 * (s / m) + 1) * (s % m)







/-- The four nontrivial cell contributions for an incident point and triangle. -/
def cellBound (p : ℤ) : ℤ :=
  1 + 2 * (p - 11) ^ 2 + minSquares 12 (12 - 2 * p) +
    2 * minSquares 12 (48 - 5 * p) + minSquares 60 (10 * p - 120)

/-- The integer defect forced by the cell-square lower bound. -/
def cellDefect (p : ℤ) : ℤ := max 0 ((cellBound p - 39 + 13) / 14)


































end Conway99Formal.CubicMetric


