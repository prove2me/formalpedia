-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch
-- name    : RamanujanLostNotebook_PartV_shared_qPoch
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T16:05:14.509879+00:00
-- url     : https://prove2.me/theorems/ef393b0f-fcc1-4006-81fc-b324364bc4a9
-- title:
--   Ramanujan's Lost Notebook Part V, shared: qPoch
-- statement:
--   Finite q-Pochhammer symbol `(a; q)_n = ∏_{k=0}^{n-1} (1 - a q^k)`, `(a; q)_0 = 1`
--   ((1.0.1), p. 1).  A polynomial in `a`, `q`: no domain restriction, no junk.
--   Reference: `(a; q)_1 = 1 - a`, `(q; q)_3 = (1 - q)(1 - q^2)(1 - q^3)`,
--   `(a; q^2)_n = qPoch a (q ^ 2) n`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- Finite q-Pochhammer symbol `(a; q)_n = ∏_{k=0}^{n-1} (1 - a q^k)`, `(a; q)_0 = 1`
((1.0.1), p. 1).  A polynomial in `a`, `q`: no domain restriction, no junk.
Reference: `(a; q)_1 = 1 - a`, `(q; q)_3 = (1 - q)(1 - q^2)(1 - q^3)`,
`(a; q^2)_n = qPoch a (q ^ 2) n`. -/
def qPoch (a q : ℂ) (n : ℕ) : ℂ :=
  ∏ k ∈ Finset.range n, (1 - a * q ^ k)

end RamanujanLostNotebook.PartV

end


