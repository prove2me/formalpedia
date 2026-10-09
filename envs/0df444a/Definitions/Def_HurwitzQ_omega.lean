-- Prove2me | Definitions.Def_HurwitzQ_omega
-- name    : HurwitzQ_omega
-- status  : Definition
-- author  : @jawneeboy
-- created : 2026-09-18T17:59:43.956976+00:00
-- url     : https://prove2.me/theorems/52946617-3705-46df-b0b2-41e4033d8ff1
-- title:
--   The half-integral Hurwitz generator
-- statement:
--   For the standard quaternion units $i,j,k$, define $$\omega=\frac{1+i+j+k}{2}.$$ This element supplies the half-integral generator used in the algebraic characterization of the Hurwitz ring.
-- source:
--   Standard definition: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003, §5.1, The Hurwitz Integral Quaternions. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345

import Mathlib.Algebra.Quaternion

open Quaternion

namespace HurwitzQ

/-- The Hurwitz generator `omega` (mathematically ω): `omega = (1 + i + j + k) / 2`,
written in coordinates. With `i, j, k` it generates the Hurwitz integers: every
half-integral Hurwitz integer is an integral one plus an integral multiple of `omega`.
It satisfies `omega ^ 2 = omega - 1` (equivalently `omega` is a root of
`X ^ 2 - X + 1`, a primitive sixth root of unity in characteristic zero) and has
norm `1`. -/
def omega : ℍ[ℚ] := ⟨(1 : ℚ) / 2, 1 / 2, 1 / 2, 1 / 2⟩

end HurwitzQ


