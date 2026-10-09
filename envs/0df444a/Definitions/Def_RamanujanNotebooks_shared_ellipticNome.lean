-- Prove2me | Definitions.Def_RamanujanNotebooks_shared_ellipticNome
-- name    : RamanujanNotebooks_shared_ellipticNome
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T21:35:13.457278+00:00
-- url     : https://prove2.me/theorems/52927081-2a45-4963-8e2d-d30294e287ae
-- title:
--   Ramanujan's Notebooks, shared: ellipticNome
-- statement:
--   The base `q = F(x) = exp(-π · _2F_1(1/2, 1/2; 1; 1 - x) / _2F_1(1/2, 1/2; 1; x)) = e^{-y}`
--   as a function of `x` (Part III, (2.1), p. 91; (6.12), p. 102).  With `x = k^2`,
--   `q = exp(-π K'/K)`, the classical nome.
--
--   Domain: `0 < x < 1`; there `0 < q < 1`, `q` is increasing in `x`, `F(1/2) = e^{-π}`,
--   `log F(x) · log F(1 - x) = π^2` (Entry 2(iii)), and `φ(F(x))^2 = z` (Entry 6).
--   Outside `0<x<1`, `ellipticY x=0` by the nonsummable `ellipticZ` values and totalized
--   division, so this definition returns `1` for `x≤0` and `x≥1`. Berndt's continuous extension
--   has `F(0)=0` and `F(1)=1`: the Lean value at zero is wrong, while the value at one agrees
--   only because of the totalized intermediate expression. Treat `x=0` separately.
--   Reference: `F(1/4) = 0.017972387008967239998…`, `F(1/2) = e^{-π} = 0.043213918263772249774…`,
--   `F((√2 - 1)^2) = e^{-π√2}`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks.

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_ellipticY

noncomputable section

namespace RamanujanNotebooks

/-- The base `q = F(x) = exp(-π · _2F_1(1/2, 1/2; 1; 1 - x) / _2F_1(1/2, 1/2; 1; x)) = e^{-y}`
as a function of `x` (Part III, (2.1), p. 91; (6.12), p. 102).  With `x = k^2`,
`q = exp(-π K'/K)`, the classical nome.

Domain: `0 < x < 1`; there `0 < q < 1`, `q` is increasing in `x`, `F(1/2) = e^{-π}`,
`log F(x) · log F(1 - x) = π^2` (Entry 2(iii)), and `φ(F(x))^2 = z` (Entry 6).
Outside `0<x<1`, `ellipticY x=0` by the nonsummable `ellipticZ` values and totalized
division, so this definition returns `1` for `x≤0` and `x≥1`. Berndt's continuous extension
has `F(0)=0` and `F(1)=1`: the Lean value at zero is wrong, while the value at one agrees
only because of the totalized intermediate expression. Treat `x=0` separately.
Reference: `F(1/4) = 0.017972387008967239998…`, `F(1/2) = e^{-π} = 0.043213918263772249774…`,
`F((√2 - 1)^2) = e^{-π√2}`. -/
def ellipticNome (x : ℝ) : ℝ :=
  Real.exp (-(ellipticY x))

end RamanujanNotebooks

end


