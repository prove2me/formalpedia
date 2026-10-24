-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
-- name    : KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:09:25.974552+00:00
-- url     : https://prove2.me/theorems/7d5d2c11-8d55-49a0-bee0-cca41a4a8959
-- title:
--   Unit bump and scaled cutoff for tempered-growth tests
-- statement:
--   For a finite-dimensional real inner-product space $E$ with its Borel measurable structure, `unitBump` is a smooth bump centered at $0$ that equals $1$ on the closed unit ball and vanishes outside the ball of radius $2$. `cutoff R x` is the scaled function $\chi_R(x)=\varphi(R^{-1}x)$, where `R` is real and $\varphi` is `unitBump`; the bundle contains no integrated generator identity.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Temperate.lean#L31-L35 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.Temperate`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
namespace FunctionalInequalities
namespace Analysis
namespace BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The bump `φ` on `E`: one on the closed unit ball, zero outside the ball of radius `2`. -/
def unitBump : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
/-- The scaled cutoff `χ_R(x) = φ(x / R)`. -/
def cutoff (R : ℝ) (x : E) : ℝ := (unitBump : ContDiffBump (0 : E)) (R⁻¹ • x)
variable (m : Measure E) [m.IsAddHaarMeasure]
end BakryEmery
end Analysis
end FunctionalInequalities


