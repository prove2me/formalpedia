-- Prove2me | Definitions.Def_RamanujanNotebooks_ch03_ch3C
-- name    : RamanujanNotebooks_ch03_ch3C
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T22:23:09.189025+00:00
-- url     : https://prove2.me/theorems/ff76488c-e406-4c77-9fd8-9cb66e30af92
-- title:
--   Ramanujan's Notebooks, Part I, Ch. 3: ch3C
-- statement:
--   The polynomials `c_k(n)` of (14.1), p. 70, for parameters `p`, `q`:
--   `c_0(n) = 1`, `c_1(n) = n`, `c_k(n) = n ∏_{j=1}^{k-1} (n + k p - j q)` for `k ≥ 2`
--   (`ch3C p q k n = c_k(n)`; the clause for `k + 1` covers `c_1` with an empty product).
--
--   Total, a polynomial in `n`, `p`, `q`.  `c_k(x) / k!` is the polynomial `f_k(x)` of the Corollary
--   on p. 69 (a Gould polynomial).  With `p = 2`, `q = 1` and `k ≥ 2`,
--   `c_k(n) = n Γ(n + 2k) / Γ(n + k + 1)` wherever the Gamma quotient is defined.
--   Reference: `ch3C p q 2 n = n (n + 2p - q)`, `ch3C 2 1 3 n = n (n + 5) (n + 4)`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 3.

import Mathlib

namespace RamanujanNotebooks

/-- The polynomials `c_k(n)` of (14.1), p. 70, for parameters `p`, `q`:
`c_0(n) = 1`, `c_1(n) = n`, `c_k(n) = n ∏_{j=1}^{k-1} (n + k p - j q)` for `k ≥ 2`
(`ch3C p q k n = c_k(n)`; the clause for `k + 1` covers `c_1` with an empty product).

Total, a polynomial in `n`, `p`, `q`.  `c_k(x) / k!` is the polynomial `f_k(x)` of the Corollary
on p. 69 (a Gould polynomial).  With `p = 2`, `q = 1` and `k ≥ 2`,
`c_k(n) = n Γ(n + 2k) / Γ(n + k + 1)` wherever the Gamma quotient is defined.
Reference: `ch3C p q 2 n = n (n + 2p - q)`, `ch3C 2 1 3 n = n (n + 5) (n + 4)`. -/
noncomputable def ch3C (p q : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | (k + 1), n => n * ∏ j ∈ Finset.range k, (n + ((k : ℝ) + 1) * p - ((j : ℝ) + 1) * q)

end RamanujanNotebooks


