-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_shared_qPoch
-- name    : RamanujanLostNotebook_PartI_shared_qPoch
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T02:11:53.610982+00:00
-- url     : https://prove2.me/theorems/07a47319-d9b8-4d41-b7c0-e92766b74a9d
-- title:
--   Ramanujan's Lost Notebook Part I, shared: qPoch
-- statement:
--   Finite q-Pochhammer symbol `(a; q)_n = (1 - a)(1 - a q) ⋯ (1 - a q^{n-1})`, with
--   `(a; q)_0 = 1` ((1.1.3), p. 9; restated with (3.1.3), p. 86).  The book shortens it to
--   `(a)_n` when the base is `q`; here the base is always written, so `(a; q^2)_n` is
--   `qPoch a (q ^ 2) n`.
--
--   Domain: all complex `a`, `q` and every `n : ℕ`.  It is a polynomial in `a` and `q`, so there
--   is no convergence condition and no junk value.  This shared definition covers only `n ≥ 0`;
--   a negative index cannot be expressed with this definition.
--   Boundary: `qPoch a q 0 = 1` (empty product) and `qPoch a q 1 = 1 - a`.
--   Reference: `(q; q)_3 = 1 - q - q^2 + q^4 + q^5 - q^6`; `qPoch (1/2) (1/5) 3 = 441/1000`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Finite q-Pochhammer symbol `(a; q)_n = (1 - a)(1 - a q) ⋯ (1 - a q^{n-1})`, with
`(a; q)_0 = 1` ((1.1.3), p. 9; restated with (3.1.3), p. 86).  The book shortens it to
`(a)_n` when the base is `q`; here the base is always written, so `(a; q^2)_n` is
`qPoch a (q ^ 2) n`.

Domain: all complex `a`, `q` and every `n : ℕ`.  It is a polynomial in `a` and `q`, so there
is no convergence condition and no junk value.  This shared definition covers only `n ≥ 0`;
a negative index cannot be expressed with this definition.
Boundary: `qPoch a q 0 = 1` (empty product) and `qPoch a q 1 = 1 - a`.
Reference: `(q; q)_3 = 1 - q - q^2 + q^4 + q^5 - q^6`; `qPoch (1/2) (1/5) 3 = 441/1000`. -/
def qPoch (a q : ℂ) (n : ℕ) : ℂ :=
  ∏ k ∈ Finset.range n, (1 - a * q ^ k)

end RamanujanLostNotebook.PartI

end


