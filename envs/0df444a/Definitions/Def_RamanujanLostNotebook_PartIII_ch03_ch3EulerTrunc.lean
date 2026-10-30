-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch03_ch3EulerTrunc
-- name    : RamanujanLostNotebook_PartIII_ch03_ch3EulerTrunc
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T09:01:15.428991+00:00
-- url     : https://prove2.me/theorems/c832eebc-6349-4976-aa1e-e25e71966f74
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 3: ch3EulerTrunc
-- statement:
--   Polynomial ∏_{j=1}^N(1-X^(d*j)); for d>0 its coefficients through degree N
--   are exactly those of (q^d;q^d)_∞. Factors beyond N have positive degree >N.
--   Used over integer Laurent coefficients; no analytic q or truncation hypothesis.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 3.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- Polynomial ∏_{j=1}^N(1-X^(d*j)); for d>0 its coefficients through degree N
are exactly those of (q^d;q^d)_∞. Factors beyond N have positive degree >N.
Used over integer Laurent coefficients; no analytic q or truncation hypothesis. -/
noncomputable def ch3EulerTrunc {R : Type*} [CommRing R] (N d : ℕ) : Polynomial R :=
  ∏ j ∈ Finset.Icc 1 N, (1 - Polynomial.X ^ (d * j))

end RamanujanLostNotebook.PartIII

end


