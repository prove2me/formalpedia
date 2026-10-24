-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
-- name    : KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:45:08.833461+00:00
-- url     : https://prove2.me/theorems/b045bfe2-78f1-481d-87f6-db8c0972cb2f
-- title:
--   Intrinsic-coordinate smooth-gradient energy
-- statement:
--   `Energy.Euclidean.toIntrinsicL2 μ` and `toAmbientL2 μ` are measure-preserving L² linear isometries induced by reconstruction and the intrinsic map between the ambient space and the direction space of the affine support. `Energy.SmoothGradient.Intrinsic.energy μ` evaluates the smooth-gradient relaxation for the intrinsic law after transporting an ambient L² class to intrinsic coordinates. The simp theorem `energy_apply` exposes this pullback formula. The construction removes energy in directions normal to the affine support but does not identify the result with Cheeger energy.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/SmoothGradient/Intrinsic/Basic.lean#L29-L161 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Basic`, definition bundle `KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

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


