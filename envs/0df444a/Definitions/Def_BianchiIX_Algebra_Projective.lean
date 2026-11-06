-- Prove2me | Definitions.Def_BianchiIX_Algebra_Projective
-- name    : BianchiIX_Algebra_Projective
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T21:03:25.68555+00:00
-- url     : https://prove2.me/theorems/4257a92a-736c-4fef-8517-17850b594c0d
-- title:
--   The exact projective vector field and core energy
-- statement:
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/Projective.lean

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Projective vector field and exact core energy, Sections 1.2 and A.2. -/

namespace BianchiIX

noncomputable section

def coupling (u v w : ℝ) : ℝ := u * (v + w - u)
def phaseVelocity (m u v w : ℝ) : ℝ :=
  -v ^ 2 + w ^ 2 + u * (v - w) - m * coupling u v w
def strongVelocity (m u v w : ℝ) : ℝ :=
  (1 - m ^ 2 - (v - w) ^ 2 + u ^ 2) * u / 2
def activeVelocity (m u v w : ℝ) : ℝ := (m - 1 - coupling u v w) * v
def weakVelocity (m u v w : ℝ) : ℝ := (-m - 1 - coupling u v w) * w
def coreEnergy (m v : ℝ) : ℝ := (m - 1) ^ 2 + v ^ 2











end

end BianchiIX


