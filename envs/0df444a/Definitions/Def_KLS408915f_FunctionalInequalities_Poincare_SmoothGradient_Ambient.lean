-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Ambient
-- name    : KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Ambient
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:46:58.595973+00:00
-- url     : https://prove2.me/theorems/74ad1a72-ea18-4284-8ba3-6d96959a47da
-- title:
--   Ambient smooth-gradient Poincaré constant
-- statement:
--   `Poincare.SmoothGradient.Ambient.constant μ` is the ENNReal optimal Poincaré constant for the sequential relaxation of globally smooth finite-gradient tests in real L²(μ). `Ambient.Holds μ C` states that a finite NNReal C is valid on the finite-energy domain of this relaxation. The energy uses the squared canonical gradient without a factor of 1/2, and no identification with Cheeger energy or a closed Sobolev form is included.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothGradient/Ambient.lean#L25-L34 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothGradient.Ambient`, definition bundle `KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Ambient`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_L2_Energy
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
open MeasureTheory
namespace FunctionalInequalities
namespace Poincare
namespace SmoothGradient
namespace Ambient
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E]
/-- The optimal Poincaré constant of the smooth-gradient sequential relaxation. -/
def constant (μ : ProbabilityMeasure E) [FiniteDimensional ℝ E]
    [BorelSpace E] [SecondCountableTopology E] : ENNReal :=
  L2Energy.constant μ (Energy.SmoothGradient.relaxation μ)
/-- Validity of a finite Poincaré constant on the finite domain of the smooth-gradient
sequential relaxation. -/
def Holds (μ : ProbabilityMeasure E) [FiniteDimensional ℝ E]
    [BorelSpace E] [SecondCountableTopology E] (C : NNReal) : Prop :=
  L2Energy.Holds μ (Energy.SmoothGradient.relaxation μ) C
end Ambient
end SmoothGradient
end Poincare
end FunctionalInequalities


