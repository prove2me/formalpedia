-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
-- name    : KLSModular_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:30:08.303924+00:00
-- url     : https://prove2.me/theorems/fd3da48f-6efa-4121-8307-74c1c05a7d2e
-- title:
--   Intrinsic-coordinate smooth-gradient energy
-- statement:
--   `Energy.Euclidean.toIntrinsicL2 μ` and `toAmbientL2 μ` are measure-preserving L² linear isometries induced by reconstruction and the intrinsic map between the ambient space and the direction space of the affine support. `Energy.SmoothGradient.Intrinsic.energy μ` evaluates the smooth-gradient relaxation for the intrinsic law after transporting an ambient L² class to intrinsic coordinates. The simp theorem `energy_apply` exposes this pullback formula. The construction removes energy in directions normal to the affine support but does not identify the result with Cheeger energy.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.SmoothGradient.Basic
--   import FunctionalInequalities.Probability.AffineSupport
--   import Mathlib.MeasureTheory.Function.LpSpace.Basic
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def toIntrinsicL2 (μ : ProbabilityMeasure E) :
--       Lp ℝ 2 (μ : Measure E) →ₗᵢ[ℝ]
--         Lp ℝ 2 (Probability.intrinsicMeasure μ).toMeasure :=
--     Lp.compMeasurePreservingₗᵢ ℝ (Probability.reconstruct μ)
--       (Probability.measurePreserving_reconstruct μ)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/SmoothGradient/Basic`](https://prove2.me/theorems/230d76a3-8a28-41f5-a6c8-38e17a1abcdd), [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81).
--
--   Theorems in source order:
--
--   - [`toAmbientL2_toIntrinsicL2`](https://prove2.me/theorems/d9b94329-b8fa-4834-8b8e-906342810111)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/SmoothGradient/Intrinsic/Basic.lean) · `FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Basic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/SmoothGradient/Intrinsic/Basic.lean#L29-L161 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Basic`, definition bundle `KLSModular_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_AffineSupport
import Mathlib.MeasureTheory.Function.LpSpace.Basic

noncomputable section
open MeasureTheory
namespace FunctionalInequalities
namespace Energy
namespace Euclidean
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]
/-- Pull an ambient `L²(μ)` function back along reconstruction from intrinsic affine coordinates.

Because reconstruction preserves the probability law, this is a real linear isometry.
-/
def toIntrinsicL2 (μ : ProbabilityMeasure E) :
    Lp ℝ 2 (μ : Measure E) →ₗᵢ[ℝ]
      Lp ℝ 2 (Probability.intrinsicMeasure μ).toMeasure :=
  Lp.compMeasurePreservingₗᵢ ℝ (Probability.reconstruct μ)
    (Probability.measurePreserving_reconstruct μ)
/-- Pull an intrinsic-coordinate `L²` function back to the original ambient probability space. -/
def toAmbientL2 (μ : ProbabilityMeasure E) :
    Lp ℝ 2 (Probability.intrinsicMeasure μ).toMeasure →ₗᵢ[ℝ]
      Lp ℝ 2 (μ : Measure E) :=
  Lp.compMeasurePreservingₗᵢ ℝ (Probability.intrinsicMap μ)
    (Probability.measurePreserving_intrinsicMap μ)
end Euclidean
end Energy
end FunctionalInequalities
namespace FunctionalInequalities
namespace Energy
namespace SmoothGradient
namespace Intrinsic
open Euclidean
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]
/-- The intrinsic-affine smooth-gradient relaxation, represented on the original `L²(μ)` space.

The functional first moves an `L²(μ)` class isometrically to the direction space of the affine
support, then evaluates the smooth-gradient relaxation of the intrinsic probability law.
-/
def energy (μ : ProbabilityMeasure E) :
    Functional (Lp ℝ 2 (μ : Measure E)) :=
  (Energy.SmoothGradient.relaxation (Probability.intrinsicMeasure μ)).comap (toIntrinsicL2 μ)
omit [CompleteSpace E] in
/-- Unfolding the intrinsic-affine relaxation exposes the isometric pullback. -/
@[simp]
theorem energy_apply (μ : ProbabilityMeasure E)
    (f : Lp ℝ 2 (μ : Measure E)) :
    energy μ f =
      Energy.SmoothGradient.relaxation (Probability.intrinsicMeasure μ) (toIntrinsicL2 μ f) :=
  rfl
end Intrinsic
end SmoothGradient
end Energy
end FunctionalInequalities


