-- Prove2me | Definitions.Def_LosslessQLTC_mConst
-- name    : LosslessQLTC_mConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:08:42.0812+00:00
-- url     : https://prove2.me/theorems/86369591-fa25-4972-813d-47569a4ad361
-- title:
--   The constant $m_{d,r}$ of (3.1)
-- statement:
--   The expansion constant of the complete $d$-partite complex at level $r$ is
--
--   $$m_{d,r}=\left(\binom{d}{r+1}\binom{d+r+1}{r+2}\right)^{-1},$$
--
--   the inverse of the product of the two binomial coefficients. For example, $m_{2,0}=1/6$, $m_{4,1}=1/120$ and $m_{4,2}=1/140$.
--
--   **Formalization Note.** The index is $j=r+1\in\mathbb N$, so `mConst d (r+1)` is $m_{d,r}$ and `mConst k r` is the $m_{k,r-1}$ of Theorem 4.10.
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), eq. (3.1), p.20

import Mathlib

namespace LosslessQLTC

/-- The constant of eq. (3.1) (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.20):
`m_{d,r} = (C(d, r+1) · C(d+r+1, r+2))⁻¹`, the inverse of the product.

**Formalization Note.** The index is `j = r + 1 ∈ ℕ`, so that `mConst d (r + 1)` is `m_{d,r}`, the
link level `r = −1` is `j = 0`, and `m_{k,r−1}` in Theorem 4.10 is `mConst k r`. -/
noncomputable def mConst (d j : ℕ) : ℝ :=
  ((d.choose j * (d + j).choose (j + 1) : ℕ) : ℝ)⁻¹

end LosslessQLTC


