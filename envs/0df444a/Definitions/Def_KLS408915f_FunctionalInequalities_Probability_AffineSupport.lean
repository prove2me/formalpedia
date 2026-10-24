-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
-- name    : KLS408915f_FunctionalInequalities_Probability_AffineSupport
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T04:57:09.373235+00:00
-- url     : https://prove2.me/theorems/6f987cf0-c7c2-4a40-8608-0ede9dff08bf
-- title:
--   Intrinsic coordinates on the affine support
-- statement:
--   For a probability measure $\mu$ on a finite-dimensional real inner-product space, `affineSupport μ` is the affine span of the topological support, while `supportPoint μ`, `origin μ`, and `coordinateEquiv μ` choose a support point, an origin on that affine carrier, and an affine isometry from its direction space to the carrier. The declarations `retraction`, `intrinsicMap`, and `intrinsicMeasure` give a measurable retraction to the affine support, intrinsic vector coordinates, and the pushforward probability law on the direction space; `measurePreserving_intrinsicMap` and `measurePreserving_reconstruct` state preservation of the corresponding measures. The support is contained in the affine support, it is closed and Borel measurable in finite dimension, almost every point lies in it, and `reconstruct_intrinsicMap_ae` states that reconstruction agrees with the ambient identity almost everywhere.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/AffineSupport.lean#L32-L213 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.AffineSupport`, definition bundle `KLS408915f_FunctionalInequalities_Probability_AffineSupport`; the repository is private at upload time).

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support

noncomputable section
open MeasureTheory
namespace FunctionalInequalities
namespace Probability
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]
/-- The affine span of the topological support of a probability measure.

This is the canonical affine carrier used here. It is not merely the topological support itself:
the latter need not be an affine space.
-/
def affineSupport (μ : ProbabilityMeasure E) : AffineSubspace ℝ E :=
  affineSpan ℝ (μ : Measure E).support
/-- The topological support is contained in its affine support. -/
theorem support_subset_affineSupport (μ : ProbabilityMeasure E) :
    (μ : Measure E).support ⊆ affineSupport μ :=
  subset_affineSpan ℝ _
section Closedness
variable [FiniteDimensional ℝ E]
/-- The affine support is closed in finite dimension. -/
theorem isClosed_affineSupport (μ : ProbabilityMeasure E) :
    IsClosed (affineSupport μ : Set E) :=
  (affineSupport μ).closed_of_finiteDimensional
variable [BorelSpace E]
/-- The affine support is Borel measurable. -/
theorem measurableSet_affineSupport (μ : ProbabilityMeasure E) :
    MeasurableSet (affineSupport μ : Set E) :=
  (isClosed_affineSupport μ).measurableSet
end Closedness
section FullMeasure
variable [SecondCountableTopology E]
/-- Almost every point lies in the affine support. -/
theorem ae_mem_affineSupport (μ : ProbabilityMeasure E) :
    ∀ᵐ x ∂(μ : Measure E), x ∈ affineSupport μ := by
  filter_upwards [Measure.support_mem_ae (μ := (μ : Measure E))] with x hx
  exact support_subset_affineSupport μ hx
/-- A chosen point of the topological support, used only to put vector coordinates on the affine
carrier. Different choices give affinely isometric coordinate presentations. -/
def supportPoint (μ : ProbabilityMeasure E) : E :=
  ((μ : Measure E).nonempty_support (IsProbabilityMeasure.ne_zero (μ : Measure E))).choose
omit [InnerProductSpace ℝ E] in
/-- The chosen point really belongs to the topological support. -/
theorem supportPoint_mem_support (μ : ProbabilityMeasure E) :
    supportPoint μ ∈ (μ : Measure E).support :=
  ((μ : Measure E).nonempty_support
    (IsProbabilityMeasure.ne_zero (μ : Measure E))).choose_spec
end FullMeasure
section Coordinates
variable [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
/-- The chosen support point, regarded as a point of the affine support. -/
def origin (μ : ProbabilityMeasure E) : affineSupport μ :=
  ⟨supportPoint μ, support_subset_affineSupport μ (supportPoint_mem_support μ)⟩
instance instNonemptyAffineSupport (μ : ProbabilityMeasure E) : Nonempty (affineSupport μ) :=
  ⟨origin μ⟩
/-- Translation by the chosen origin identifies the direction vector space with the affine
support isometrically. -/
def coordinateEquiv (μ : ProbabilityMeasure E) :
    (affineSupport μ).direction ≃ᵃⁱ[ℝ] affineSupport μ :=
  AffineIsometryEquiv.vaddConst ℝ (origin μ)
/-- A measurable retraction onto the affine support. Outside the full-measure carrier it uses the
chosen origin; this arbitrary branch has no effect on the induced probability law. -/
def retraction (μ : ProbabilityMeasure E) (x : E) : affineSupport μ :=
  by
    classical
    exact if hx : x ∈ affineSupport μ then ⟨x, hx⟩ else origin μ
omit [CompleteSpace E] in
/-- The affine-support retraction is measurable. -/
theorem measurable_retraction (μ : ProbabilityMeasure E) : Measurable (retraction μ) := by
  classical
  change Measurable (fun x ↦
    if hx : x ∈ affineSupport μ then (⟨x, hx⟩ : affineSupport μ) else origin μ)
  exact Measurable.dite measurable_id measurable_const (measurableSet_affineSupport μ)
/-- Intrinsic vector coordinates of an ambient point. -/
def intrinsicMap (μ : ProbabilityMeasure E) (x : E) : (affineSupport μ).direction :=
  (coordinateEquiv μ).symm (retraction μ x)
omit [CompleteSpace E] in
/-- The intrinsic-coordinate map is measurable. -/
theorem measurable_intrinsicMap (μ : ProbabilityMeasure E) : Measurable (intrinsicMap μ) :=
  (coordinateEquiv μ).symm.continuous.measurable.comp (measurable_retraction μ)
/-- The original probability law expressed on the direction vector space of its affine support. -/
def intrinsicMeasure (μ : ProbabilityMeasure E) :
    ProbabilityMeasure (affineSupport μ).direction :=
  μ.map (measurable_intrinsicMap μ).aemeasurable
/-- Reconstruction from intrinsic vector coordinates back into the ambient space, bundled as an
affine isometry. -/
def reconstruct (μ : ProbabilityMeasure E) : (affineSupport μ).direction →ᵃⁱ[ℝ] E :=
  (affineSupport μ).subtypeₐᵢ.comp (coordinateEquiv μ).toAffineIsometry
omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Reconstruction is measurable. -/
theorem measurable_reconstruct (μ : ProbabilityMeasure E) : Measurable (reconstruct μ) :=
  (reconstruct μ).continuous.measurable
omit [CompleteSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Reconstruction after taking intrinsic coordinates is the ambient identity almost everywhere. -/
theorem reconstruct_intrinsicMap_ae (μ : ProbabilityMeasure E) :
    (fun x ↦ reconstruct μ (intrinsicMap μ x)) =ᵐ[(μ : Measure E)] fun x ↦ x := by
  filter_upwards [ae_mem_affineSupport μ] with x hx
  simp [reconstruct, intrinsicMap, coordinateEquiv, retraction, hx]
omit [CompleteSpace E] in
/-- Taking intrinsic coordinates preserves the probability law by construction. -/
theorem measurePreserving_intrinsicMap (μ : ProbabilityMeasure E) :
    MeasurePreserving (intrinsicMap μ) (μ : Measure E) (intrinsicMeasure μ : Measure _) :=
  ⟨measurable_intrinsicMap μ, rfl⟩
omit [CompleteSpace E] in
/-- Reconstructing the intrinsic law gives back the original ambient probability law exactly. -/
theorem measurePreserving_reconstruct (μ : ProbabilityMeasure E) :
    MeasurePreserving (reconstruct μ) (intrinsicMeasure μ : Measure _) (μ : Measure E) := by
  refine ⟨measurable_reconstruct μ, ?_⟩
  rw [intrinsicMeasure, ProbabilityMeasure.toMeasure_map,
    Measure.map_map (measurable_reconstruct μ) (measurable_intrinsicMap μ)]
  have hcomp : reconstruct μ ∘ intrinsicMap μ =ᵐ[(μ : Measure E)] id := by
    filter_upwards [reconstruct_intrinsicMap_ae μ] with x hx
    simpa only [Function.comp_apply, id_eq] using hx
  rw [Measure.map_congr hcomp, Measure.map_id]
end Coordinates
end Probability
end FunctionalInequalities


