-- Prove2me | Definitions.Def_IntADSat_Supplement_catBound
-- name    : IntADSat_Supplement_catBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:52:31.40671+00:00
-- url     : https://prove2.me/theorems/8a10b331-97ea-452b-a052-9f4c91ad9ff4
-- title:
--   Order bound $m_n=\lceil12\sqrt{n\log n}+6\rceil$
-- statement:
--   For $n\ge0$,
--   $$m_n=\Big\lceil 12\sqrt{n\log n}+6\Big\rceil,$$
--   with the natural logarithm. It bounds the order of the test caterpillars in Theorem 1.2 and Corollary C.2.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Corollary C.2, p.21 (PDF 22); Theorem 1.2, p.2 (PDF 3)

import Mathlib

set_option autoImplicit false

namespace IntADSat.Supplement

/-- `m_n = ⌈12 √(n log n) + 6⌉` (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Corollary C.2, p.21 (PDF 22); Theorem 1.2, p.2 (PDF 3)), the bound
on the order of the test caterpillars.

**Formalization Note** `log` is the natural logarithm (`Real.log`), the square root covers `n log n`, and
the ceiling is `Nat.ceil`. -/
noncomputable def catBound (n : ℕ) : ℕ :=
  ⌈12 * Real.sqrt ((n : ℝ) * Real.log n) + 6⌉₊

end IntADSat.Supplement


