-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch04_ch04ScaledPoch
-- name    : RamanujanLostNotebook_PartII_ch04_ch04ScaledPoch
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T07:40:21.00064+00:00
-- url     : https://prove2.me/theorems/e1fbdb02-5eb0-4814-8381-4b3416e96617
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 4: ch04ScaledPoch
-- statement:
--   Homogeneous finite q-Pochhammer product, used to remove the reciprocal parameter
--   in Chapter 4: `H(b,x;q,n) = ∏_{0≤k<n}(b-x q^k)`.
--   For b≠0 it is `b^n (x/b;q)_n`; the finite product is its polynomial continuation
--   at b=0. This is not a second definition of the shared q-Pochhammer symbol.
--   The empty product is 1; at n=1 the value is b-x. At b=0 it is
--   (-x)^n q^(n(n-1)/2). It introduces no convergence or nonvanishing premise.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 4.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Homogeneous finite q-Pochhammer product, used to remove the reciprocal parameter
in Chapter 4: `H(b,x;q,n) = ∏_{0≤k<n}(b-x q^k)`.
For b≠0 it is `b^n (x/b;q)_n`; the finite product is its polynomial continuation
at b=0. This is not a second definition of the shared q-Pochhammer symbol.
The empty product is 1; at n=1 the value is b-x. At b=0 it is
(-x)^n q^(n(n-1)/2). It introduces no convergence or nonvanishing premise. -/
def ch04ScaledPoch (b x q : ℂ) (n : ℕ) : ℂ :=
  ∏ k ∈ Finset.range n, (b - x * q ^ k)

end RamanujanLostNotebook.PartII

end


