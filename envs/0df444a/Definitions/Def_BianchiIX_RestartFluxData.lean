-- Prove2me | Definitions.Def_BianchiIX_RestartFluxData
-- name    : BianchiIX_RestartFluxData
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-06T04:37:28.498499+00:00
-- url     : https://prove2.me/theorems/1559b044-ab2f-44fa-9422-5c966da67002
-- title:
--   Angular and shear annuli and logarithmic costs in section flux
-- statement:
--   For log-wall coordinates
--   $(v,l,r)$ set $M=\max(e^{-l},e^{-r})$. The angular region has
--   $0<M\le d$ and $|v|\le LM$; the shear region has $0<|v|\le d$ and
--   $M\le\epsilon |v|$. Restricting the corresponding radius to $(a,2a]$
--   gives a dyadic annulus. The clipped densities, layer costs and flux
--   constants describe integrals over excluded labels in these annuli.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/tree/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Module
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped Topology ENNReal

def clippedPowerDensity (ell B δ x : ℝ) : ℝ := min ell (B * x ^ δ) / x





















def clippedPowerDensityTwo (ell B δ x : ℝ) : ℝ :=
  (∫ y in (0 : ℝ)..1, clippedPowerDensity ell (B * x ^ δ) δ y) / x



















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def logarithmicFluxConstant (C δ : ℝ) : ℝ :=
  (1 + (Real.log C + 1 + 2 * δ) + (Real.log C + 1 + 2 * δ) ^ 2 / 2) / δ ^ 2



def logarithmicLayerCost (a C δ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ y in Ioo (0 : ℝ) 1,
    ENNReal.ofReal (min a ((C * a ^ (-2 * δ)) * (x * y) ^ δ) / (x * y))







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def logarithmicLayerCostOne (a C σ : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (min a ((C * a ^ (-2 * σ)) * t ^ σ) / t)

def logarithmicFluxConstantOne (C σ : ℝ) : ℝ := (1 + Real.log C + 2 * σ) / σ







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def angularSection (d L : ℝ) : Set SectionCoordinates :=
  {z | max (Real.exp (-z 1)) (Real.exp (-z 2)) ≤ d ∧
    |z 0| ≤ L * max (Real.exp (-z 1)) (Real.exp (-z 2))}

def angularSectionAnnulus (a L : ℝ) : Set SectionCoordinates :=
  {z | max (Real.exp (-z 1)) (Real.exp (-z 2)) ∈ Ioc a (2 * a) ∧
    |z 0| ≤ L * max (Real.exp (-z 1)) (Real.exp (-z 2))}











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def shearSection (d ε : ℝ) : Set SectionCoordinates :=
  {z | |z 0| ∈ Ioc 0 d ∧ Real.exp (-z 1) ≤ ε * |z 0| ∧ Real.exp (-z 2) ≤ ε * |z 0|}

def shearSectionAnnulus (a ε : ℝ) : Set SectionCoordinates :=
  {z | |z 0| ∈ Ioc a (2 * a) ∧ Real.exp (-z 1) ≤ ε * |z 0| ∧ Real.exp (-z 2) ≤ ε * |z 0|}













end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def angularFailureFluxConstant (L σ : ℝ) : ℝ := 640 * Real.sqrt 3 * (102400 * (L + 1)) ^ σ





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal Classical

def shearFailureFluxConstant (σ : ℝ) : ℝ := 640 * Real.sqrt 3 * (800 : ℝ) ^ σ











end BianchiIX

end
end


