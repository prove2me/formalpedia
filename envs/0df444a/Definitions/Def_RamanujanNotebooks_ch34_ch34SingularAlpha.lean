-- Prove2me | Definitions.Def_RamanujanNotebooks_ch34_ch34SingularAlpha
-- name    : RamanujanNotebooks_ch34_ch34SingularAlpha
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T08:04:03.18651+00:00
-- url     : https://prove2.me/theorems/a441f289-60aa-4664-bf57-8fc5d993e47a
-- title:
--   Ramanujan's Notebooks, Part V, Ch. 34: ch34SingularAlpha
-- statement:
--   The singular modulus `α_r = k_r^2` of Part V, Chapter 34 (pp. 183, 188), for a real index `r`: the
--   square of the elliptic modulus belonging to the nome `q = e^{-π√r}`, written through theta functions,
--   `α_r = 1 - φ(-q)^4 / φ(q)^4`, with the shared `thetaPhi` at the real points `±e^{-π√r}` (cast to `ℂ`).
--   The quotient is a real number in `(0, 1)`; the real part is taken only to return a real number.  The
--   book defines `α_n` by `F(α_n) = e^{-π√n}` with the nome function `F` of its (2.3); that the two
--   definitions agree is the inversion formula of Part III, Chapter 17, and is stated as a theorem of the
--   chapter (equation (2.6)).
--
--   Domain: `r > 0`; there `0 < α_r < 1`, `α_r` decreases in `r`, `α_(1/r) = 1 - α_r` and `α_1 = 1/2`.
--   Outside: for `r ≤ 0`, `Real.sqrt r = 0`, the arguments are `∓1`, the theta series are not summable and the
--   value has no meaning; every use carries a positive index.
--   Reference: `α_1 = 1/2`, `α_2 = (√2 - 1)^2 = 0.1715728752538099024…`,
--   `α_3 = (2 - √3)/4 = 0.066987298107780676618…`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part V (Springer, 1998), Chapter 34.

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_thetaPhi

namespace RamanujanNotebooks

/-- The singular modulus `α_r = k_r^2` of Part V, Chapter 34 (pp. 183, 188), for a real index `r`: the
square of the elliptic modulus belonging to the nome `q = e^{-π√r}`, written through theta functions,
`α_r = 1 - φ(-q)^4 / φ(q)^4`, with the shared `thetaPhi` at the real points `±e^{-π√r}` (cast to `ℂ`).
The quotient is a real number in `(0, 1)`; the real part is taken only to return a real number.  The
book defines `α_n` by `F(α_n) = e^{-π√n}` with the nome function `F` of its (2.3); that the two
definitions agree is the inversion formula of Part III, Chapter 17, and is stated as a theorem of the
chapter (equation (2.6)).

Domain: `r > 0`; there `0 < α_r < 1`, `α_r` decreases in `r`, `α_(1/r) = 1 - α_r` and `α_1 = 1/2`.
Outside: for `r ≤ 0`, `Real.sqrt r = 0`, the arguments are `∓1`, the theta series are not summable and the
value has no meaning; every use carries a positive index.
Reference: `α_1 = 1/2`, `α_2 = (√2 - 1)^2 = 0.1715728752538099024…`,
`α_3 = (2 - √3)/4 = 0.066987298107780676618…`. -/
noncomputable def ch34SingularAlpha (r : ℝ) : ℝ :=
  1 - (thetaPhi (-((Real.exp (-(Real.pi * Real.sqrt r)) : ℝ) : ℂ)) ^ 4 /
        thetaPhi ((Real.exp (-(Real.pi * Real.sqrt r)) : ℝ) : ℂ) ^ 4).re

end RamanujanNotebooks


