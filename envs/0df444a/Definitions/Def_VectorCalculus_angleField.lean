-- Prove2me | Definitions.Def_VectorCalculus_angleField
-- name    : VectorCalculus_angleField
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T00:06:23.169611+00:00
-- url     : https://prove2.me/theorems/911ab556-0b7b-404c-a189-783269aca995
-- title:
--   The planar field $\mathbf{F} = (-y/(x^2+y^2),\, x/(x^2+y^2))$
-- statement:
--   The planar vector field
--
--   $$\mathbf F(x,y) = \left(-\frac{y}{x^2+y^2},\ \frac{x}{x^2+y^2}\right),$$
--
--   singular at the origin, whose natural potential is the polar angle $\tan^{-1}(y/x)$. It is written here as a function defined on all of $\mathbb R^2$, its value at the origin being $(0,0)$ by the convention that division by zero yields zero.
-- source:
--   David Tong, Vector Calculus, University of Cambridge Part IA Mathematical Tripos lecture notes, http://www.damtp.cam.ac.uk/user/tong/vc.html, §1.3.4 (pp. 25–26), the field $\mathbf F = (-y/(x^2+y^2), x/(x^2+y^2))$ on $\mathbb R^2 - \{0,0\}$

import Mathlib

namespace VectorCalculus

/-- The planar vector field `F = (-y/(x²+y²), x/(x²+y²))`, written as a total function
on `ℝ²`; at the origin both components evaluate to `0` because division by zero is `0`. -/
noncomputable def angleField : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun z =>
  ![-z 1 / ((z 0) ^ 2 + (z 1) ^ 2), z 0 / ((z 0) ^ 2 + (z 1) ^ 2)]

end VectorCalculus


