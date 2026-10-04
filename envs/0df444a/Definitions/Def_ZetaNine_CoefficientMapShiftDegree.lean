-- Prove2me | Definitions.Def_ZetaNine_CoefficientMapShiftDegree
-- name    : ZetaNine_CoefficientMapShiftDegree
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-03T21:52:16.793713+00:00
-- url     : https://prove2.me/theorems/37ba0a3d-3bd9-4bce-85b8-4f85c9e9586f
-- title:
--   Actual rational polynomial shift difference operator
-- statement:
--   For natural $n$, define actual rational polynomials $A_n=(X-(n+1))(X+n)^{10}$, $B_n=X^{10}(X+2n+1)$ and the actual linear shift difference $D_n(H)=A_nH-B_nH(X+1)$. These are three genuine polynomial definitions with no degree, kernel, rational-function or inverse premise.
-- source:
--   Zeta(9) actual polynomial shift operator: missions/zeta9/research/coefficient-map-shift-degree-2026-10-04.md. Frozen source SHA256 96efe64f218c07a9d941136af1b4a0874bca9627c01be262c53e4445e0876953. The relationship to the rational telescoper is proved separately; it is not an input to these polynomial endpoints.

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Reverse

set_option autoImplicit false
noncomputable section
namespace ZetaNine.CoefficientMapShiftDegree

open Polynomial

def shiftA (n : ℕ) : ℚ[X] := (X - C ((n : ℚ) + 1)) * (X + C (n : ℚ)) ^ 10

def shiftB (n : ℕ) : ℚ[X] := X ^ 10 * (X + C (2 * (n : ℚ) + 1))

def shiftDifference (n : ℕ) (H : ℚ[X]) : ℚ[X] :=
  shiftA n * H - shiftB n * H.comp (X + C 1)

end ZetaNine.CoefficientMapShiftDegree


