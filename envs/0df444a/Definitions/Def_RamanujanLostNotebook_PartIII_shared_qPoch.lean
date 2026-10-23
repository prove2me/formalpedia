-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_shared_qPoch
-- name    : RamanujanLostNotebook_PartIII_shared_qPoch
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T02:20:52.218345+00:00
-- url     : https://prove2.me/theorems/f30cf995-1d95-46af-aaaf-8870055f5785
-- title:
--   Ramanujan's Lost Notebook Part III, shared: qPoch
-- statement:
--   Finite q-Pochhammer symbol `(a; q)_n = ∏_{k=0}^{n-1} (1 - a q^k)` for each nonnegative
--   integer `n`, so `(a; q)_0 = 1` (unnumbered display before (2.1.1), p. 9; restated in
--   Section 8.1, p. 217).  The book shortens it to `(a)_n` when the base is `q`; here the base is
--   always written, so `(a; q^5)_n` is `qPoch a (q ^ 5) n`.
--
--   Domain: all complex `a`, `q` and every `n : ℕ`.  It is a polynomial in `a` and `q`, so there
--   is no convergence condition and no junk value.  This shared definition covers only `n ≥ 0`.
--   Boundary: `qPoch a q 0 = 1` (empty product) and `qPoch a q 1 = 1 - a`.
--   Reference: `(q; q)_3 = 1 - q - q^2 + q^4 + q^5 - q^6`; `qPoch (1/2) (1/5) 3 = 441/1000`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- Finite q-Pochhammer symbol `(a; q)_n = ∏_{k=0}^{n-1} (1 - a q^k)` for each nonnegative
integer `n`, so `(a; q)_0 = 1` (unnumbered display before (2.1.1), p. 9; restated in
Section 8.1, p. 217).  The book shortens it to `(a)_n` when the base is `q`; here the base is
always written, so `(a; q^5)_n` is `qPoch a (q ^ 5) n`.

Domain: all complex `a`, `q` and every `n : ℕ`.  It is a polynomial in `a` and `q`, so there
is no convergence condition and no junk value.  This shared definition covers only `n ≥ 0`.
Boundary: `qPoch a q 0 = 1` (empty product) and `qPoch a q 1 = 1 - a`.
Reference: `(q; q)_3 = 1 - q - q^2 + q^4 + q^5 - q^6`; `qPoch (1/2) (1/5) 3 = 441/1000`. -/
def qPoch (a q : ℂ) (n : ℕ) : ℂ :=
  ∏ k ∈ Finset.range n, (1 - a * q ^ k)

end RamanujanLostNotebook.PartIII

end


