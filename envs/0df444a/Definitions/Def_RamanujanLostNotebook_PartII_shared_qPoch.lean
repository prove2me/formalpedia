-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_shared_qPoch
-- name    : RamanujanLostNotebook_PartII_shared_qPoch
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T02:16:55.107242+00:00
-- url     : https://prove2.me/theorems/b6a7f526-3728-4c3b-9ded-b70ced6b6cba
-- title:
--   Ramanujan's Lost Notebook Part II, shared: qPoch
-- statement:
--   Finite q-Pochhammer symbol `(a; q)_n = (1 - a)(1 - a q) ⋯ (1 - a q^{n-1})` for each
--   nonnegative integer `n`, with `(a; q)_0 = 1` ((1.1.2), p. 5).  The book shortens it to `(a)_n`
--   when only the base `q` occurs; here the base is always written, so `(a; q^2)_n` is
--   `qPoch a (q ^ 2) n`.
--
--   Domain: all complex `a`, `q` and every `n : ℕ`.  It is a polynomial in `a` and `q`, so there
--   is no convergence condition and no junk value.  The book's extension to negative `n`,
--   `(a; q)_n = (a; q)_∞ / (a q^n; q)_∞` ((1.1.7), p. 6), is not covered by this definition.
--   Boundary: `qPoch a q 0 = 1` (empty product) and `qPoch a q 1 = 1 - a`.
--   Reference: `(q; q)_3 = 1 - q - q^2 + q^4 + q^5 - q^6`; `qPoch (1/2) (1/5) 3 = 441/1000`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Finite q-Pochhammer symbol `(a; q)_n = (1 - a)(1 - a q) ⋯ (1 - a q^{n-1})` for each
nonnegative integer `n`, with `(a; q)_0 = 1` ((1.1.2), p. 5).  The book shortens it to `(a)_n`
when only the base `q` occurs; here the base is always written, so `(a; q^2)_n` is
`qPoch a (q ^ 2) n`.

Domain: all complex `a`, `q` and every `n : ℕ`.  It is a polynomial in `a` and `q`, so there
is no convergence condition and no junk value.  The book's extension to negative `n`,
`(a; q)_n = (a; q)_∞ / (a q^n; q)_∞` ((1.1.7), p. 6), is not covered by this definition.
Boundary: `qPoch a q 0 = 1` (empty product) and `qPoch a q 1 = 1 - a`.
Reference: `(q; q)_3 = 1 - q - q^2 + q^4 + q^5 - q^6`; `qPoch (1/2) (1/5) 3 = 441/1000`. -/
def qPoch (a q : ℂ) (n : ℕ) : ℂ :=
  ∏ k ∈ Finset.range n, (1 - a * q ^ k)

end RamanujanLostNotebook.PartII

end


