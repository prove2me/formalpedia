-- Prove2me | Definitions.Def_RamanujanNotebooks_ch34_ch34InvariantJ
-- name    : RamanujanNotebooks_ch34_ch34InvariantJ
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T08:06:50.497979+00:00
-- url     : https://prove2.me/theorems/53ebc5be-86ad-449a-aa60-adfe8a6ad8c3
-- title:
--   Ramanujan's Notebooks, Part V, Ch. 34: ch34InvariantJ
-- statement:
--   Ramanujan's invariant `J_r` of Part V, Chapter 34, (11.3), p. 309, for a real index `r`:
--   `J_r = (1 - 16 α_r (1 - α_r)) / (8 (4 α_r (1 - α_r))^(1/3))`, where `α_r` is the chapter's singular
--   modulus `ch34SingularAlpha r`.  By the book's (11.6), `J_n = -(1/32) j((3 + √(-n))/2)^(1/3)` with the
--   modular `j`-invariant (real cube root).  The cube root is a real power of the positive number
--   `4 α_r (1 - α_r)`.
--
--   Domain: `r > 0`; there `0 < 4 α_r (1 - α_r) ≤ 1`.
--   Outside: for `r ≤ 0` the value has no meaning; every use carries a positive index.
--   Reference: `J_3 = 0`, `J_11 = 1`, `J_43 = 30`, `J_7 = 15/32 = 0.46875`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part V (Springer, 1998), Chapter 34.

import Mathlib
import Definitions.Def_RamanujanNotebooks_ch34_ch34SingularAlpha

namespace RamanujanNotebooks

/-- Ramanujan's invariant `J_r` of Part V, Chapter 34, (11.3), p. 309, for a real index `r`:
`J_r = (1 - 16 α_r (1 - α_r)) / (8 (4 α_r (1 - α_r))^(1/3))`, where `α_r` is the chapter's singular
modulus `ch34SingularAlpha r`.  By the book's (11.6), `J_n = -(1/32) j((3 + √(-n))/2)^(1/3)` with the
modular `j`-invariant (real cube root).  The cube root is a real power of the positive number
`4 α_r (1 - α_r)`.

Domain: `r > 0`; there `0 < 4 α_r (1 - α_r) ≤ 1`.
Outside: for `r ≤ 0` the value has no meaning; every use carries a positive index.
Reference: `J_3 = 0`, `J_11 = 1`, `J_43 = 30`, `J_7 = 15/32 = 0.46875`. -/
noncomputable def ch34InvariantJ (r : ℝ) : ℝ :=
  (1 - 16 * (ch34SingularAlpha r * (1 - ch34SingularAlpha r))) /
    (8 * (4 * (ch34SingularAlpha r * (1 - ch34SingularAlpha r))) ^ ((1 : ℝ) / 3))

end RamanujanNotebooks


