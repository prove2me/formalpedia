-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_ellipticZ
-- name    : RamanujanNotebooks_shared_ellipticZ
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:28:18.378842+00:00
-- url     : https://prove2.me/theorems/3a15b7b4-5d74-4702-ac61-9aa5b8429c41
-- title:
--   Ramanujan's Notebooks, shared: ellipticZ
-- statement:
--   Ramanujan's `z = _2F_1(1/2, 1/2; 1; x)` as a function of `x` (Part III, (6.2), p. 101;
--   Part V, (1.2), p. 90).  With `x = k^2`, `z = (2/π) K(k)` ((6.11), p. 102) and
--   `z = φ(q)^2` for `q = ellipticNome x` (Entry 6, (6.4)); both are theorems.
--
--   Domain: `0 ≤ x < 1` (Berndt: `0 < x < 1`); the series also converges for `-1 < x < 0`.
--   `z(0) = 1`; `z` is increasing on `[0, 1)` and unbounded as `x → 1`.
--   Outside: for `|x| ≥ 1` the family is not summable (at `x = -1` it converges only
--   conditionally) and Lean returns `0`.
--   Reference: `z(1/2) = √π / Γ(3/4)^2`, `z(1/4) = 1.0731820071493643750…`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_hyp2F1R

noncomputable section

namespace RamanujanNotebooks

/-- Ramanujan's `z = _2F_1(1/2, 1/2; 1; x)` as a function of `x` (Part III, (6.2), p. 101;
Part V, (1.2), p. 90).  With `x = k^2`, `z = (2/π) K(k)` ((6.11), p. 102) and
`z = φ(q)^2` for `q = ellipticNome x` (Entry 6, (6.4)); both are theorems.

Domain: `0 ≤ x < 1` (Berndt: `0 < x < 1`); the series also converges for `-1 < x < 0`.
`z(0) = 1`; `z` is increasing on `[0, 1)` and unbounded as `x → 1`.
Outside: for `|x| ≥ 1` the family is not summable (at `x = -1` it converges only
conditionally) and Lean returns `0`.
Reference: `z(1/2) = √π / Γ(3/4)^2`, `z(1/4) = 1.0731820071493643750…`. -/
def ellipticZ (x : ℝ) : ℝ :=
  hyp2F1R (1 / 2) (1 / 2) 1 x

end RamanujanNotebooks

end


