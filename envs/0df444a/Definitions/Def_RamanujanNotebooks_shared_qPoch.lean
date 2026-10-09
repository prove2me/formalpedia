-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_qPoch
-- name    : RamanujanNotebooks_shared_qPoch
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:17:56.126994+00:00
-- url     : https://prove2.me/theorems/1ea5f203-57a9-4185-9563-6e2cfc751eea
-- title:
--   Ramanujan's Notebooks, shared: qPoch
-- statement:
--   Finite q-Pochhammer symbol `(a)_k = (a; q)_k = (1 - a)(1 - aq) ⋯ (1 - aq^{k-1})`,
--   `(a; q)_0 = 1` (Part III, p. 12; (0.3), p. 88).  A polynomial in `a`, `q`: no domain
--   restriction, no junk.  Argument order: `qPoch a q n`.
--   Reference: `(a; q)_1 = 1 - a`, `(q; q)_3 = (1 - q)(1 - q^2)(1 - q^3)`,
--   `(a; q^2)_n = qPoch a (q ^ 2) n`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib

noncomputable section

namespace RamanujanNotebooks

/-- Finite q-Pochhammer symbol `(a)_k = (a; q)_k = (1 - a)(1 - aq) ⋯ (1 - aq^{k-1})`,
`(a; q)_0 = 1` (Part III, p. 12; (0.3), p. 88).  A polynomial in `a`, `q`: no domain
restriction, no junk.  Argument order: `qPoch a q n`.
Reference: `(a; q)_1 = 1 - a`, `(q; q)_3 = (1 - q)(1 - q^2)(1 - q^3)`,
`(a; q^2)_n = qPoch a (q ^ 2) n`. -/
def qPoch (a q : ℂ) (n : ℕ) : ℂ :=
  ∏ k ∈ Finset.range n, (1 - a * q ^ k)

end RamanujanNotebooks

end


