-- Prove2me | Definitions.Def_ZInQCurve
-- name    : ZInQCurve
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T19:09:15.030096+00:00
-- url     : https://prove2.me/theorems/e4b1cb52-e496-43ab-96a7-0e5c031fc46c
-- title:
--   The short Weierstrass curve $y^2=x^3+Ax$
-- statement:
--   This bundle defines, over any field $F$, the short Weierstrass curve $\mathrm{shortCurve}(A)$ with equation $y^2=x^3+Ax$, i.e. the Weierstrass curve with coefficients $a_1=a_2=a_3=a_6=0$ and $a_4=A$. It is used for the congruent number curves $C_d=\mathrm{shortCurve}(-d^2)$ over $\mathbb{Q}$.
-- source:
--   https://github.com/elliotglazer/diophantine-z-q/blob/964d7dd71f253091dbc5eac793b78cc56d1fcc73/ZInQKernel/Model/Field/ShortWeierstrass.lean#L18-L26

import Mathlib

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F]

/-- The short Weierstrass curve y^2 = x^3 + A x. -/
def shortCurve (A : F) : WeierstrassCurve F where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := A
  a₆ := 0

end ZInQ


