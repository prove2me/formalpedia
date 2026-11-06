-- Prove2me | Definitions.Def_BianchiIX_Algebra_MatchingPhase
-- name    : BianchiIX_Algebra_MatchingPhase
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T07:37:34.585568+00:00
-- url     : https://prove2.me/theorems/62956ece-7f60-4535-ba18-9ce139afb738
-- title:
--   Matching phase and its interaction kernel
-- statement:
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   Set $n(a,b)=\sqrt{a^2+b^2}$, $j(a,b)=1/[n(a,b)(n(a,b)+a)]$,
--   $$\phi(m,v,w)=n(m+1,v)+n(m-1,w)-m,$$
--   $$h=(m+1)/n(m+1,v)+(m-1)/n(m-1,w)-1,$$
--   $$q=mh+v^2/n(m+1,v)+w^2/n(m-1,w),\qquad
--   j_*=j(m+1,v)-j(m-1,w).$$
--   The matching phase rate is $(vw)^2j_*-uh(v-w)-\kappa q$.
--   All inverse operations use total real-field division.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/MatchingPhase.lean

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
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

namespace BianchiIX

def phaseNorm (a b : ℝ) : ℝ := Real.sqrt (a ^ 2 + b ^ 2)

def matchingPhase (m v w : ℝ) : ℝ := phaseNorm (m + 1) v + phaseNorm (m - 1) w - m

def matchingPhaseSlope (m v w : ℝ) : ℝ :=
  (m + 1) / phaseNorm (m + 1) v + (m - 1) / phaseNorm (m - 1) w - 1

def matchingPhaseWeight (m v w : ℝ) : ℝ :=
  m * matchingPhaseSlope m v w + v ^ 2 / phaseNorm (m + 1) v + w ^ 2 / phaseNorm (m - 1) w

def phaseNormKernel (a b : ℝ) : ℝ := 1 / (phaseNorm a b * (phaseNorm a b + a))

def matchingPhaseKernel (m v w : ℝ) : ℝ := phaseNormKernel (m + 1) v - phaseNormKernel (m - 1) w

def matchingPhaseRate (m u v w : ℝ) : ℝ :=
  (v * w) ^ 2 * matchingPhaseKernel m v w - u * matchingPhaseSlope m v w * (v - w) -
    coupling u v w * matchingPhaseWeight m v w





















end BianchiIX


