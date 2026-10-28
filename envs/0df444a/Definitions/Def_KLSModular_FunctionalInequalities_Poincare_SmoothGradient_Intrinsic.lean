-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothGradient_Intrinsic
-- name    : KLSModular_FunctionalInequalities_Poincare_SmoothGradient_Intrinsic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:34:57.352006+00:00
-- url     : https://prove2.me/theorems/a8e3faa6-c047-4d96-8dd5-12b0b86d8284
-- title:
--   Intrinsic smooth-gradient Poincaré constant
-- statement:
--   `Poincare.SmoothGradient.Intrinsic.constant μ` applies the generic real-L² Poincaré optimizer to the intrinsic-affine smooth-gradient relaxation `Energy.SmoothGradient.Intrinsic.energy μ`. The variance is the intrinsic L²(μ) variance of the original probability law, while the energy is evaluated through the intrinsic-coordinate presentation. The definition does not assert a Cheeger, spectral, or KLS identification.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Closed
--   import FunctionalInequalities.Poincare.L2.Energy
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def constant (μ : ProbabilityMeasure E) : ENNReal :=
--     L2Energy.constant μ
--       (Energy.SmoothGradient.Intrinsic.energy μ)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/SmoothGradient/Intrinsic/Closed`](https://prove2.me/theorems/68a98bd0-06ea-4f37-962c-da6ced53e691), [`Poincare/L2/Energy`](https://prove2.me/theorems/2c373d63-eba6-4063-92d2-2450951b5927).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/SmoothGradient/Intrinsic.lean) · `FunctionalInequalities.Poincare.SmoothGradient.Intrinsic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothGradient/Intrinsic.lean#L29-L32 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothGradient.Intrinsic`, definition bundle `KLSModular_FunctionalInequalities_Poincare_SmoothGradient_Intrinsic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Closed
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_L2_Energy

noncomputable section
open MeasureTheory
namespace FunctionalInequalities
namespace Poincare
namespace SmoothGradient
namespace Intrinsic
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]
/-- The optimal Poincaré constant of the intrinsic-affine smooth-gradient relaxation. -/
def constant (μ : ProbabilityMeasure E) : ENNReal :=
  L2Energy.constant μ
    (Energy.SmoothGradient.Intrinsic.energy μ)
end Intrinsic
end SmoothGradient
end Poincare
end FunctionalInequalities


