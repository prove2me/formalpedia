-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Poincare_CovarianceGradient_Intrinsic
-- name    : KLSModular_FunctionalInequalities_Poincare_CovarianceGradient_Intrinsic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:24:48.909992+00:00
-- url     : https://prove2.me/theorems/1f8dcbca-2143-4720-b0ae-d14854806427
-- title:
--   Intrinsic affine covariance-gradient Poincaré constant
-- statement:
--   For a finite-dimensional real Hilbert space E and a probability measure μ on E, `Poincare.CovarianceGradient.Intrinsic.constant` applies the generic real-L² optimizer `L2Energy.constant` to the intrinsic law of μ and the intrinsic covariance-gradient energy. The corresponding `Holds` predicate records validity of a finite NNReal constant on the finite-energy domain of that relaxation. The definitions make no finiteness, log-concavity, closability, isotropy, or KLS assertion.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.CovarianceGradient.Basic
--   import FunctionalInequalities.Poincare.L2.Energy
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def constant (μ : ProbabilityMeasure E) : ENNReal :=
--     L2Energy.constant (Probability.intrinsicMeasure μ) (Energy.CovarianceGradient.Intrinsic.energy μ)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/CovarianceGradient/Basic`](https://prove2.me/theorems/517395bc-0a9a-4b82-b89c-ca3b5281db43), [`Poincare/L2/Energy`](https://prove2.me/theorems/2c373d63-eba6-4063-92d2-2450951b5927).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/CovarianceGradient/Intrinsic.lean) · `FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/CovarianceGradient/Intrinsic.lean#L40-L48 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic`, definition bundle `KLSModular_FunctionalInequalities_Poincare_CovarianceGradient_Intrinsic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_L2_Energy

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


