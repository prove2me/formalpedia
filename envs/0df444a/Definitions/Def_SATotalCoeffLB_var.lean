-- Prove2me | Definitions.Def_SATotalCoeffLB_var
-- name    : SATotalCoeffLB_var
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:45.513485+00:00
-- url     : https://prove2.me/theorems/22260fda-3ff3-4e35-9b9e-75fe549bee00
-- title:
--   The variable $v$ as a $\pm1$-valued function
-- statement:
--   For a variable $v \in V$, the element $v$ of the Boolean quotient ring is the function
--
--   $$
--   v(x) = (-1)^{x_v}, \qquad x \in \mathbb F_2^V,
--   $$
--
--   so $v = +1$ when its bit is $0$ and $v = -1$ when its bit is $1$ (the $\{\pm1\}$ encoding of p.23).
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), p.23 (the {±1} encoding)

import Mathlib
import Definitions.Def_SATotalCoeffLB_CubeFn

namespace SATotalCoeffLB

/-- **The variable `v`** as an element of the Boolean quotient ring: its value at the cube point
`x` is `(-1)^{x v}`, i.e. `+1` when the bit is `0` and `-1` when it is `1` (the `{±1}` encoding of
p.23 of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)). -/
noncomputable def var {V : Type*} (v : V) : CubeFn V := fun x => (-1 : ℝ) ^ (x v).val

end SATotalCoeffLB


