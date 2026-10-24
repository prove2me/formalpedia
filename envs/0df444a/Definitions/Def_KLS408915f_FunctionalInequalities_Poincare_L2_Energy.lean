-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_L2_Energy
-- name    : KLS408915f_FunctionalInequalities_Poincare_L2_Energy
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:36:38.445001+00:00
-- url     : https://prove2.me/theorems/942501b2-0de8-4d29-902a-e3e44ae5c11c
-- title:
--   Poincaré constants for extended energies on real L²
-- statement:
--   For a probability measure μ on a measurable space and an extended energy functional on real L²(μ), `TestFamily.ofL2Energy` uses exactly the finite-energy domain as its test type. Each test has intrinsic L² variance `L2.variance μ f.1` and the finite energy value certified by the domain subtype. `L2Energy.constant` is the resulting extended optimal Poincaré constant, while `L2Energy.Holds` states that a finite NNReal constant is valid for every finite-energy test. No closedness, quadraticity, or Markov property is assumed.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/L2/Energy.lean#L27-L63 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.L2.Energy`, definition bundle `KLS408915f_FunctionalInequalities_Poincare_L2_Energy`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory
namespace FunctionalInequalities
namespace Poincare
universe u
variable {α : Type u} [MeasurableSpace α]
namespace TestFamily
/-- The finite-energy domain of an extended functional on real `L²(μ)`, equipped with
intrinsic `L²` variance and the functional's finite value. -/
def ofL2Energy (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) : TestFamily where
  Test := energy.domain
  variance f := L2.variance μ f.1
  energy f := energy.finiteValue f
/-- Variance in the induced test family is intrinsic `L²` variance. -/
@[simp]
theorem ofL2Energy_variance (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α)))
    (f : energy.domain) :
    (ofL2Energy μ energy).variance f = L2.variance μ f.1 :=
  rfl
/-- Energy in the induced test family is the finite value certified by the domain subtype. -/
@[simp]
theorem ofL2Energy_energy (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α)))
    (f : energy.domain) :
    (ofL2Energy μ energy).energy f = energy.finiteValue f :=
  rfl
end TestFamily
namespace L2Energy
/-- The optimal extended Poincaré constant of an energy on real `L²(μ)`. -/
def constant (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) : ENNReal :=
  (TestFamily.ofL2Energy μ energy).constant
/-- A finite Poincaré constant is valid on every finite-energy `L²` test. -/
def Holds (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) (C : NNReal) : Prop :=
  (TestFamily.ofL2Energy μ energy).Holds C
end L2Energy
end Poincare
end FunctionalInequalities


