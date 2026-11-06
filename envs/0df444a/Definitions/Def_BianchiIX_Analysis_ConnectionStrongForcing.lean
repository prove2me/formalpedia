-- Prove2me | Definitions.Def_BianchiIX_Analysis_ConnectionStrongForcing
-- name    : BianchiIX_Analysis_ConnectionStrongForcing
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T09:13:05.972206+00:00
-- url     : https://prove2.me/theorems/6e2b80b5-d205-40df-9e02-02556fb52dbc
-- title:
--   The shifted strong-wall forcing and its integral budget
-- statement:
--   For real $\mu,u_0,u,p,x$, set
--   $$S_\mu(u_0,u,p,x)=|x|[32u+16384u_0(u+p^2/\mu^5)],$$
--   $$B^S_\mu(u,p,x)=|x|(64u/\mu+32768u^2/\mu+4096up^2/\mu^4).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ConnectionStrongForcing.lean

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





def connectionStrongSource (μ u₀ u p x : ℝ) : ℝ :=
  |x| * (32 * u + 16384 * u₀ * (u + p ^ 2 / μ ^ 5))

def connectionStrongSourceBudget (μ u p x : ℝ) : ℝ :=
  |x| * (64 * u / μ + 32768 * u ^ 2 / μ + 4096 * u * p ^ 2 / μ ^ 4)





end BianchiIX


