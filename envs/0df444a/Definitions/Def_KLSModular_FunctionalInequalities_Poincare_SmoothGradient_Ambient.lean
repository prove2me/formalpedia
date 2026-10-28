-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothGradient_Ambient
-- name    : KLSModular_FunctionalInequalities_Poincare_SmoothGradient_Ambient
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:31:33.546038+00:00
-- url     : https://prove2.me/theorems/33180a6e-515f-4d0d-bef8-794f71f3df9a
-- title:
--   Ambient smooth-gradient Poincaré constant
-- statement:
--   `Poincare.SmoothGradient.Ambient.constant μ` is the ENNReal optimal Poincaré constant for the sequential relaxation of globally smooth finite-gradient tests in real L²(μ). `Ambient.Holds μ C` states that a finite NNReal C is valid on the finite-energy domain of this relaxation. The energy uses the squared canonical gradient without a factor of 1/2, and no identification with Cheeger energy or a closed Sobolev form is included.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.SmoothGradient.Basic
--   import FunctionalInequalities.Poincare.L2.Energy
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def constant (μ : ProbabilityMeasure E) [FiniteDimensional ℝ E]
--       [BorelSpace E] [SecondCountableTopology E] : ENNReal :=
--     L2Energy.constant μ (Energy.SmoothGradient.relaxation μ)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/SmoothGradient/Basic`](https://prove2.me/theorems/230d76a3-8a28-41f5-a6c8-38e17a1abcdd), [`Poincare/L2/Energy`](https://prove2.me/theorems/2c373d63-eba6-4063-92d2-2450951b5927).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/SmoothGradient/Ambient.lean) · `FunctionalInequalities.Poincare.SmoothGradient.Ambient` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothGradient/Ambient.lean#L25-L34 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothGradient.Ambient`, definition bundle `KLSModular_FunctionalInequalities_Poincare_SmoothGradient_Ambient`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_L2_Energy

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


