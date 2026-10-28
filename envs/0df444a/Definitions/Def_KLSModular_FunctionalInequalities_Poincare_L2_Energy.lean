-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Poincare_L2_Energy
-- name    : KLSModular_FunctionalInequalities_Poincare_L2_Energy
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:24:02.63254+00:00
-- url     : https://prove2.me/theorems/2c373d63-eba6-4063-92d2-2450951b5927
-- title:
--   Poincaré constants for extended energies on real L²
-- statement:
--   For a probability measure μ on a measurable space and an extended energy functional on real L²(μ), `TestFamily.ofL2Energy` uses exactly the finite-energy domain as its test type. Each test has intrinsic L² variance `L2.variance μ f.1` and the finite energy value certified by the domain subtype. `L2Energy.constant` is the resulting extended optimal Poincaré constant, while `L2Energy.Holds` states that a finite NNReal constant is valid for every finite-energy test. No closedness, quadraticity, or Markov property is assumed.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.Form.Functional
--   import FunctionalInequalities.L2.MeanVariance
--   import FunctionalInequalities.Poincare.SmoothTest.Optimal
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def ofL2Energy (μ : ProbabilityMeasure α)
--       (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) : TestFamily where
--     Test := energy.domain
--     variance f := L2.variance μ f.1
--     energy f := energy.finiteValue f
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/Form/Functional`](https://prove2.me/theorems/4dfa9356-1019-4d47-ba3e-299615584765), [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8), [`Poincare/SmoothTest/Optimal`](https://prove2.me/theorems/1bd7b12a-ba10-47ca-83e9-4d99a34876b9).
--
--   Theorems in source order:
--
--   - [`constant_eq_of_linearIsometryEquiv`](https://prove2.me/theorems/6ef866fb-b080-4fd9-8723-b37080782c4a)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/L2/Energy.lean) · `FunctionalInequalities.Poincare.L2.Energy` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/L2/Energy.lean#L27-L63 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.L2.Energy`, definition bundle `KLSModular_FunctionalInequalities_Poincare_L2_Energy`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Optimal

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


