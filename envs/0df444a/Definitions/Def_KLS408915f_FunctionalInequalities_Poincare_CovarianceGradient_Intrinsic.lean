-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_CovarianceGradient_Intrinsic
-- name    : KLS408915f_FunctionalInequalities_Poincare_CovarianceGradient_Intrinsic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:37:11.254+00:00
-- url     : https://prove2.me/theorems/91d397b9-ba56-45cf-894b-bb4a18e8b88b
-- title:
--   Intrinsic affine covariance-gradient Poincaré constant
-- statement:
--   For a finite-dimensional real Hilbert space E and a probability measure μ on E, `Poincare.CovarianceGradient.Intrinsic.constant` applies the generic real-L² optimizer `L2Energy.constant` to the intrinsic law of μ and the intrinsic covariance-gradient energy. The corresponding `Holds` predicate records validity of a finite NNReal constant on the finite-energy domain of that relaxation. The definitions make no finiteness, log-concavity, closability, isotropy, or KLS assertion.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/CovarianceGradient/Intrinsic.lean#L40-L48 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic`, definition bundle `KLS408915f_FunctionalInequalities_Poincare_CovarianceGradient_Intrinsic`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_L2_Energy
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
open MeasureTheory
namespace FunctionalInequalities
namespace Poincare
namespace CovarianceGradient
namespace Intrinsic
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]
/-- The affine covariance Poincaré constant `C_P^aff(μ)`: the optimal extended constant of the
affine covariance relaxation on the intrinsic law. -/
def constant (μ : ProbabilityMeasure E) : ENNReal :=
  L2Energy.constant (Probability.intrinsicMeasure μ) (Energy.CovarianceGradient.Intrinsic.energy μ)
/-- Validity of a finite constant on the finite-energy domain of the affine covariance
relaxation of the intrinsic law. -/
def Holds (μ : ProbabilityMeasure E) (C : NNReal) : Prop :=
  L2Energy.Holds (Probability.intrinsicMeasure μ) (Energy.CovarianceGradient.Intrinsic.energy μ) C
end Intrinsic
end CovarianceGradient
end Poincare
end FunctionalInequalities


