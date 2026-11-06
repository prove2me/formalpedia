-- Prove2me | Definitions.Def_BianchiIX_Analysis_ConnectionGrowingFeedbackBounds
-- name    : BianchiIX_Analysis_ConnectionGrowingFeedbackBounds
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T09:17:04.259326+00:00
-- url     : https://prove2.me/theorems/5d11ac0c-861a-4978-9591-608216d73151
-- title:
--   Growing-wall feedback source and its finite budget
-- statement:
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   For initial walls $u_0,w_0$ and $y=(m,u,v,w)$ define
--   $$S=1024u(1+w^2/(\mu w_0))+
--   64(u+(vw)^2/\mu^5)(12800u_0+64w^2/(\mu w_0))
--   +32(uw+(vw)^2/\mu^3)/w_0,$$
--   $$B=\frac{u_0(7296+1638400u_0+204800w_0^2/\mu^3)
--   +w_0(2048/\mu^5+8/\mu)}{\mu}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ConnectionGrowingFeedbackBounds.lean

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Analysis_ConnectionGrowingSources
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
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul

noncomputable section

namespace BianchiIX



def connectionGrowingFeedbackSource (μ u w : ℝ) (y : ProjectiveState) : ℝ :=
  1024 * y 1 * (1 + y 3 ^ 2 / (μ * w)) +
    64 * (y 1 + (y 2 * y 3) ^ 2 / μ ^ 5) * (12800 * u + 64 * y 3 ^ 2 / (μ * w)) +
    connectionGrowingPhaseSource μ w y

def connectionGrowingFeedbackBudget (μ u w : ℝ) : ℝ :=
  (u * (7296 + 1638400 * u + 204800 * w ^ 2 / μ ^ 3) + w * (2048 / μ ^ 5 + 8 / μ)) / μ







end BianchiIX


