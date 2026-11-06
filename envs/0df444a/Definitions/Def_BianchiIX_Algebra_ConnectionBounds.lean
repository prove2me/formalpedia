-- Prove2me | Definitions.Def_BianchiIX_Algebra_ConnectionBounds
-- name    : BianchiIX_Algebra_ConnectionBounds
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T07:37:31.833641+00:00
-- url     : https://prove2.me/theorems/e03da6bf-0a91-4842-9201-cdc883001fd0
-- title:
--   Connection clock speed and strong wall rate
-- statement:
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   Put $c=u(v+w-u)$, $s(m,u,v,w)=m-1-c$,
--   $b(m,u,v,w)=(1-m^2-(v-w)^2+u^2)/2$,
--   $D(m,u,v,w)=3+m^2+K(u,v,w)$, and $r(m,v)=\sqrt{(m-1)^2+v^2}$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/ConnectionBounds.lean

import Definitions.Def_BianchiIX_Algebra_Projective
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

noncomputable section

namespace BianchiIX

def connectionSpeed (m u v w : ℝ) : ℝ := m - 1 - coupling u v w

def connectionStrongRate (m u v w : ℝ) : ℝ :=
  (1 - m ^ 2 - (v - w) ^ 2 + u ^ 2) / 2





















end BianchiIX


