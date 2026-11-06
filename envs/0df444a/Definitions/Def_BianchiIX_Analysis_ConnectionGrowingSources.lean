-- Prove2me | Definitions.Def_BianchiIX_Analysis_ConnectionGrowingSources
-- name    : BianchiIX_Analysis_ConnectionGrowingSources
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T09:13:16.609642+00:00
-- url     : https://prove2.me/theorems/10fd50ba-ce06-46e6-b3b2-cd70c6a4e669
-- title:
--   Forcing from a unit ordinary growing-wall variation
-- statement:
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   For entry wall $w_0$ and $y=(m,u,v,w)$ define
--   $$S^u=\frac{32}{w_0}\left(\frac{w^2+vw}{\mu}+uw\right),\quad
--   S^v=\frac{64}{w_0}\left(\frac{w^2}{\mu}+\mu uw\right),\quad
--   S^\phi=\frac{32}{w_0}\left(uw+\frac{(vw)^2}{\mu^3}\right).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ConnectionGrowingSources.lean

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
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

def connectionGrowingStrongSource (μ w : ℝ) (y : ProjectiveState) : ℝ :=
  32 * ((y 3 ^ 2 + y 2 * y 3) / μ + y 1 * y 3) / w

def connectionGrowingWeakSource (μ w : ℝ) (y : ProjectiveState) : ℝ :=
  64 * (y 3 ^ 2 / μ + μ * y 1 * y 3) / w

def connectionGrowingPhaseSource (μ w : ℝ) (y : ProjectiveState) : ℝ :=
  32 * (y 1 * y 3 + (y 2 * y 3) ^ 2 / μ ^ 3) / w







end BianchiIX


