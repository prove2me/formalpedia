-- Prove2me | Definitions.Def_BianchiIX_Analysis_ConnectionFeedbackBounds
-- name    : BianchiIX_Analysis_ConnectionFeedbackBounds
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T09:12:57.263218+00:00
-- url     : https://prove2.me/theorems/34abd070-6cbc-4eeb-a0b6-890c98ce2083
-- title:
--   Phase feedback rate and integrated budget
-- statement:
--   For entry amplitudes $u,p$, define the feedback budget
--   $$\Lambda_\mu(u,p)=64\left(\frac{2u}{\mu^3}+\frac{p^2}{4\mu^3}\right)
--   +8192\left(\frac{4u}{\mu^2}+\frac{p^2}{16\mu^3}\right).$$
--
--   The rate is $k_\mu(\tau,u,p)=64(u/\mu^2+p^2/\mu^4)
--   +8192\tau(u+p^2/\mu^5)$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ConnectionFeedbackBounds.lean

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

def connectionPhaseFeedbackRate (μ τ u p : ℝ) : ℝ :=
  64 * (u / μ ^ 2 + p ^ 2 / μ ^ 4) + 8192 * τ * (u + p ^ 2 / μ ^ 5)

def connectionPhaseFeedbackBudget (μ u p : ℝ) : ℝ :=
  64 * (2 * u / μ ^ 3 + p ^ 2 / (4 * μ ^ 3)) +
    8192 * (4 * u / μ ^ 2 + p ^ 2 / (16 * μ ^ 3))











end BianchiIX


